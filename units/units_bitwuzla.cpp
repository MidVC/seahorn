#ifdef WITH_BITWUZLA
/* Unit tests for the Bitwuzla encoder (marshal_bitwuzla), solver and model */
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Smt/BitwuzlaModelImpl.hh"
#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"

#include "llvm/Support/raw_ostream.h"

#include "boost/lexical_cast.hpp"

#include <functional>
#include <string>

#include "sea_doctest.hh" // doctest is last to avoid name clash
// -- with DOCTEST_CONFIG_IMPLEMENT, doctest includes macOS's <mach/boolean.h>,
// -- which defines TRUE and FALSE as macros
#undef TRUE
#undef FALSE

using namespace expr;
using namespace seahorn;
using seahorn::solver::bitwuzla_solver_impl;
using seahorn::solver::marshal_bitwuzla;
using seahorn::solver::Solver;
using seahorn::solver::SolverResult;
using seahorn::solver::UnsupportedExpr;
namespace bz = bitwuzla;

namespace {
struct Env {
  ExprFactory efac;
  bz::TermManager tm;
  marshal_bitwuzla m{tm};

  Expr bvc(const std::string &name, unsigned w) {
    return bv::bvConst(mkTerm<std::string>(name, efac), w);
  }
  Expr boolc(const std::string &name) {
    return bind::boolConst(mkTerm<std::string>(name, efac));
  }
  Expr num(long v, unsigned w) {
    return bv::bvnum(expr::mpz_class(v), w, efac);
  }
  Expr bvsort(unsigned w) { return bv::bvsort(w, efac); }
  Expr arrayc(const std::string &name, unsigned iw, unsigned vw) {
    return bind::mkConst(mkTerm<std::string>(name, efac),
                         sort::arrayTy(bvsort(iw), bvsort(vw)));
  }
  /// (lambda (x) body), where body uses the bound variable \p x
  /// (bind::abs returns \p body itself when \p x does not occur in it)
  Expr lambda(Expr x, Expr body) {
    return bind::abs<LAMBDA>(std::array<Expr, 1>{x}, body);
  }
  /// (lambda (x) v) for a \p v without x, as opsem's FilledMemory builds it
  Expr constLambda(Expr x, Expr v) { return mk<LAMBDA>(bind::fname(x), v); }

  bz::Result check(Expr e) {
    bz::Bitwuzla s(tm);
    s.assert_formula(m.encode_term(e));
    return s.check_sat();
  }
  bool valid(Expr e) { return check(mk<NEG>(e)) == bz::Result::UNSAT; }
};

using BinOp = std::function<Expr(Expr, Expr)>;
template <typename Op> BinOp binop() {
  return [](Expr a, Expr b) { return mk<Op>(a, b); };
}

/// Z3's value of a variable-free \p t (through the existing EZ3 path)
Expr z3Value(Env &env, EZ3 &z3, Expr t, Expr r) {
  ZSolver<EZ3> solver(z3);
  solver.assertExpr(mk<EQ>(r, t));
  REQUIRE(bool(solver.solve()));
  return solver.getModel().eval(r);
}
} // namespace

TEST_CASE("bitwuzla.sorts") {
  Env env;
  CHECK(env.m.encode_sort(sort::boolTy(env.efac)).is_bool());
  CHECK(env.m.encode_sort(env.bvsort(13)).bv_size() == 13);
  bz::Sort arr =
      env.m.encode_sort(sort::arrayTy(env.bvsort(64), env.bvsort(8)));
  CHECK(arr.is_array());
  CHECK(arr.array_index().bv_size() == 64);
  CHECK(arr.array_element().bv_size() == 8);
  CHECK_THROWS_AS(env.m.encode_sort(sort::intTy(env.efac)), UnsupportedExpr);
  CHECK_THROWS_AS(env.m.encode_sort(sort::realTy(env.efac)), UnsupportedExpr);
}

TEST_CASE("bitwuzla.constants") {
  Env env;
  Expr x = env.bvc("x", 8);
  bz::Term tx = env.m.encode_term(x);
  CHECK(tx.is_const());
  CHECK(tx.sort().bv_size() == 8);
  CHECK(tx.symbol().value().get() == "x");
  // -- the cache gives one Bitwuzla constant per SeaHorn constant
  CHECK(env.m.encode_term(x) == tx);
  CHECK(env.m.encode_term(mk<BADD>(x, x)) == env.m.encode_term(mk<BADD>(x, x)));
  CHECK(env.m.decls().size() == 1);

  // -- constants of different sorts with the same name stay different
  Expr x16 = env.bvc("x", 16);
  CHECK(env.m.encode_term(x16) != tx);
  CHECK(env.m.decls().size() == 2);

  CHECK(env.m.encode_term(env.boolc("b")).sort().is_bool());
  CHECK(env.m.encode_term(env.arrayc("A", 64, 8)).sort().is_array());
}

TEST_CASE("bitwuzla.numerals") {
  Env env;
  // -- wider than 64 bits: 2^100 - 1
  expr::mpz_class big("1267650600228229401496703205375");
  Expr n100 = bv::bvnum(big, 128, env.efac);
  Expr two100 = bv::bvnum(expr::mpz_class("1267650600228229401496703205376"),
                          128, env.efac);
  CHECK(env.m.encode_term(n100).value<std::string>(10) ==
        "1267650600228229401496703205375");
  CHECK(env.valid(mk<EQ>(n100, mk<BADD>(two100, env.num(-1, 128)))));
  // -- negative and too-large values are taken modulo 2^width
  CHECK(env.m.encode_term(env.num(-1, 8)).value<std::string>(10) == "255");
  CHECK(env.m.encode_term(env.num(256 + 7, 8)).value<std::string>(10) == "7");
  CHECK(env.m.encode_term(env.num(-128, 8)).value<std::string>(10) == "128");
}

TEST_CASE("bitwuzla.bv operators agree with z3") {
  Env env;
  EZ3 z3(env.efac);
  const unsigned w = 3;

  // -- division and remainder by zero are included: both follow SMT-LIB
  std::vector<std::pair<const char *, BinOp>> ops = {
      {"bvand", binop<BAND>()},
      {"bvor", binop<BOR>()},
      {"bvxor", binop<BXOR>()},
      {"bvnand", binop<BNAND>()},
      {"bvnor", binop<BNOR>()},
      {"bvxnor", binop<BXNOR>()},
      {"bvadd", binop<BADD>()},
      {"bvsub", binop<BSUB>()},
      {"bvmul", binop<BMUL>()},
      {"bvudiv", binop<BUDIV>()},
      {"bvsdiv", binop<BSDIV>()},
      {"bvurem", binop<BUREM>()},
      {"bvsrem", binop<BSREM>()},
      {"bvsmod", binop<BSMOD>()},
      {"bvshl", binop<BSHL>()},
      {"bvlshr", binop<BLSHR>()},
      {"bvashr", binop<BASHR>()},
      {"concat", binop<BCONCAT>()},
      {"bvult", binop<BULT>()},
      {"bvslt", binop<BSLT>()},
      {"bvule", binop<BULE>()},
      {"bvsle", binop<BSLE>()},
      {"bvuge", binop<BUGE>()},
      {"bvsge", binop<BSGE>()},
      {"bvugt", binop<BUGT>()},
      {"bvsgt", binop<BSGT>()},
      {"=", binop<EQ>()},
      {"distinct", binop<NEQ>()},
      // -- unary operators, applied to the first argument
      {"bvnot", [](Expr a, Expr) { return mk<BNOT>(a); }},
      {"bvneg", [](Expr a, Expr) { return mk<BNEG>(a); }},
      {"bvredand", [](Expr a, Expr) { return mk<BREDAND>(a); }},
      {"bvredor", [](Expr a, Expr) { return mk<BREDOR>(a); }},
  };

  bz::Bitwuzla bzla(env.tm);
  unsigned disagreements = 0;
  for (auto &op : ops) {
    for (long a = 0; a < (1 << w); ++a) {
      for (long b = 0; b < (1 << w); ++b) {
        Expr t = op.second(env.num(a, w), env.num(b, w));
        // -- the sort of the result, as Bitwuzla sees it
        bz::Sort s = env.m.encode_term(t).sort();
        Expr r = s.is_bool() ? env.boolc("r") : env.bvc("r", s.bv_size());
        Expr expected = z3Value(env, z3, t, r);

        bzla.push(1);
        bzla.assert_formula(env.m.encode_term(mk<NEQ>(t, expected)));
        bool agrees = bzla.check_sat() == bz::Result::UNSAT;
        bzla.pop(1);
        if (!agrees) {
          ++disagreements;
          MESSAGE(op.first << " " << a << " " << b << ": z3 says "
                           << boost::lexical_cast<std::string>(*expected));
        }
      }
    }
  }
  CHECK(disagreements == 0);
}

TEST_CASE("bitwuzla.overflow predicates agree with z3 and with arithmetic") {
  Env env;
  EZ3 z3(env.efac);

  // -- expected truth value from exact integer arithmetic, given a and b as
  // -- signed and as unsigned values, and the width
  struct Pred {
    const char *name;
    BinOp mkop;
    std::function<bool(long, long, long, long, unsigned)> exact;
  };
  auto smin = [](unsigned w) { return -(1L << (w - 1)); };
  auto smax = [](unsigned w) { return (1L << (w - 1)) - 1; };
  auto umax = [](unsigned w) { return (1L << w) - 1; };
  std::vector<Pred> preds = {
      {"uadd_no_overflow", binop<UADD_NO_OVERFLOW>(),
       [&](long, long, long ua, long ub, unsigned w) {
         return ua + ub <= umax(w);
       }},
      {"usub_no_underflow", binop<USUB_NO_UNDERFLOW>(),
       [&](long, long, long ua, long ub, unsigned) { return ua - ub >= 0; }},
      {"umul_no_overflow", binop<UMUL_NO_OVERFLOW>(),
       [&](long, long, long ua, long ub, unsigned w) {
         return ua * ub <= umax(w);
       }},
      {"sadd_no_overflow", binop<SADD_NO_OVERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa + sb <= smax(w);
       }},
      {"sadd_no_underflow", binop<SADD_NO_UNDERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa + sb >= smin(w);
       }},
      {"ssub_no_overflow", binop<SSUB_NO_OVERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa - sb <= smax(w);
       }},
      {"ssub_no_underflow", binop<SSUB_NO_UNDERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa - sb >= smin(w);
       }},
      {"smul_no_overflow", binop<SMUL_NO_OVERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa * sb <= smax(w);
       }},
      {"smul_no_underflow", binop<SMUL_NO_UNDERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa * sb >= smin(w);
       }},
  };

  bz::Bitwuzla bzla(env.tm);
  unsigned checked = 0, z3_wrong = 0, bzla_wrong = 0;
  for (unsigned w = 1; w <= 4; ++w) {
    for (auto &p : preds) {
      for (long ua = 0; ua <= umax(w); ++ua) {
        for (long ub = 0; ub <= umax(w); ++ub) {
          long sa = ua > smax(w) ? ua - (1L << w) : ua;
          long sb = ub > smax(w) ? ub - (1L << w) : ub;
          bool expected = p.exact(sa, sb, ua, ub, w);
          Expr t = p.mkop(env.num(ua, w), env.num(ub, w));

          ZSolver<EZ3> solver(z3);
          solver.assertExpr(t);
          bool z3_says = bool(solver.solve());

          bzla.push(1);
          bzla.assert_formula(env.m.encode_term(t));
          bool bzla_says = bzla.check_sat() == bz::Result::SAT;
          bzla.pop(1);

          ++checked;
          if (z3_says != expected) {
            ++z3_wrong;
            MESSAGE("z3 " << p.name << " w=" << w << " " << sa << " " << sb);
          }
          if (bzla_says != expected) {
            ++bzla_wrong;
            MESSAGE("bitwuzla " << p.name << " w=" << w << " " << sa << " "
                                << sb);
          }
        }
      }
    }
  }
  // -- 9 predicates x (4 + 16 + 64 + 256) argument pairs
  CHECK(checked == 9 * 340);
  CHECK(z3_wrong == 0);
  CHECK(bzla_wrong == 0);
}

TEST_CASE("bitwuzla.extract, extend, concat, repeat, rotate") {
  Env env;
  Expr ab = env.num(0xAB, 8);
  CHECK(env.valid(mk<EQ>(bv::extract(7, 4, ab), env.num(0xA, 4))));
  CHECK(env.valid(mk<EQ>(bv::extract(3, 0, ab), env.num(0xB, 4))));
  CHECK(env.valid(mk<EQ>(bv::sext(env.num(0x8, 4), 8), env.num(0xF8, 8))));
  CHECK(env.valid(mk<EQ>(bv::zext(env.num(0x8, 4), 8), env.num(0x08, 8))));
  // -- the first argument of concat is the most significant
  CHECK(env.valid(mk<EQ>(mk<BCONCAT>(env.num(0xA, 4), env.num(0xB, 4)), ab)));
  CHECK(
      env.valid(mk<EQ>(mk<BCONCAT>(env.num(1, 1), env.num(0, 1), env.num(1, 1)),
                       env.num(5, 3))));
  CHECK(env.valid(
      mk<EQ>(mk<BREPEAT>(mkTerm<unsigned>(2, env.efac), env.num(0xA, 4)),
             env.num(0xAA, 8))));
  Expr x81 = env.num(0x81, 8);
  CHECK(env.valid(mk<EQ>(mk<BROTATE_LEFT>(mkTerm<unsigned>(1, env.efac), x81),
                         env.num(0x03, 8))));
  CHECK(env.valid(mk<EQ>(mk<BROTATE_RIGHT>(mkTerm<unsigned>(1, env.efac), x81),
                         env.num(0xC0, 8))));
  // -- n-ary forms of the associative operators
  Expr x = env.bvc("x", 8);
  CHECK(env.valid(
      mk<EQ>(mknary<BADD>(ExprVector{x, x, x}), mk<BMUL>(x, env.num(3, 8)))));
  CHECK(env.valid(mk<EQ>(mknary<BAND>(ExprVector{x, ab, x}), mk<BAND>(x, ab))));
}

TEST_CASE("bitwuzla.boolean operators") {
  Env env;
  Expr p = env.boolc("p"), q = env.boolc("q");
  Expr t = mk<TRUE>(env.efac), f = mk<FALSE>(env.efac);
  CHECK(env.valid(mk<IMPL>(f, p)));
  CHECK(env.valid(
      mk<IFF>(mk<NEG>(mk<AND>(p, q)), mk<OR>(mk<NEG>(p), mk<NEG>(q)))));
  CHECK(env.valid(mk<IFF>(mk<XOR>(p, q), mk<NEQ>(p, q))));
  CHECK(env.valid(
      mk<EQ>(mk<ITE>(t, env.num(1, 4), env.num(2, 4)), env.num(1, 4))));
  CHECK(env.valid(mknary<OR>(ExprVector{p, q, mk<NEG>(p)})));
  CHECK(env.check(mknary<AND>(ExprVector{p, q, mk<NEG>(p)})) ==
        bz::Result::UNSAT);
}

TEST_CASE("bitwuzla.arrays") {
  Env env;
  Expr A = env.arrayc("A", 8, 8);
  Expr i = env.bvc("i", 8), j = env.bvc("j", 8);
  Expr v = env.num(7, 8), u = env.num(9, 8);
  CHECK(env.valid(mk<EQ>(op::array::select(op::array::store(A, i, v), i), v)));
  CHECK(env.valid(mk<IMPL>(
      mk<NEQ>(i, j), mk<EQ>(op::array::select(op::array::store(A, i, v), j),
                            op::array::select(A, j)))));
  // -- extensionality
  CHECK(env.valid(mk<EQ>(op::array::store(op::array::store(A, i, v), i, u),
                         op::array::store(A, i, u))));
  Expr c = op::array::constArray(env.bvsort(8), v);
  CHECK(env.valid(mk<EQ>(op::array::select(c, i), v)));
}

TEST_CASE("bitwuzla.uninterpreted functions") {
  Env env;
  Expr bv8 = env.bvsort(8);
  Expr f = bind::fdecl(mkTerm<std::string>("f", env.efac),
                       ExprVector{bv8, bv8, bv8});
  Expr x = env.bvc("x", 8), y = env.bvc("y", 8);
  Expr fxy = bind::fapp(f, x, y), fyx = bind::fapp(f, y, x);
  CHECK(env.valid(mk<IMPL>(mk<EQ>(x, y), mk<EQ>(fxy, fyx))));
  CHECK(env.check(mk<NEQ>(fxy, fyx)) == bz::Result::SAT);
  CHECK(env.m.encode_term(fxy).sort().bv_size() == 8);
}

TEST_CASE("bitwuzla.lambdas") {
  Env env;
  Expr A = env.arrayc("A", 8, 8);
  Expr p = env.bvc("p", 8), q = env.bvc("q", 8);
  Expr v = env.num(7, 8);
  Expr a = env.bvc("a", 8);
  // -- (lambda (a) (ite (= a p) 7 (select A a))): a store, as opsem builds it
  Expr L = env.lambda(a, mk<ITE>(mk<EQ>(a, p), v, op::array::select(A, a)));
  CHECK(env.m.encode_term(L).sort().is_fun());

  SUBCASE("application and select on a lambda") {
    CHECK(env.valid(mk<EQ>(bind::fapp(L, p), v)));
    CHECK(env.valid(mk<EQ>(op::array::select(L, p), v)));
    CHECK(env.valid(mk<IMPL>(
        mk<NEQ>(q, p), mk<EQ>(bind::fapp(L, q), op::array::select(A, q)))));
  }
  SUBCASE("store into a lambda") {
    Expr S = op::array::store(L, q, env.num(9, 8));
    CHECK(env.valid(mk<EQ>(op::array::select(S, q), env.num(9, 8))));
    CHECK(
        env.valid(mk<IMPL>(mk<NEQ>(q, p), mk<EQ>(op::array::select(S, p), v))));
  }
  SUBCASE("ite between lambdas") {
    // -- Bitwuzla aborts on a plain ITE of lambdas; the encoder avoids it
    Expr c = env.boolc("c");
    Expr L0 = env.constLambda(a, env.num(0, 8));
    Expr I = mk<ITE>(c, L, L0);
    CHECK(env.valid(mk<EQ>(bind::fapp(I, p), mk<ITE>(c, v, env.num(0, 8)))));
    Expr J = mk<ITE>(c, A, L0); // array and lambda
    CHECK(env.valid(
        mk<IMPL>(mk<NEG>(c), mk<EQ>(op::array::select(J, p), env.num(0, 8)))));
  }
  SUBCASE("equality with a lambda") {
    // -- opsem's PHI encoding asserts (= mem lambda), with mem an array
    Expr B = env.arrayc("B", 8, 8);
    CHECK(env.check(mk<AND>(mk<EQ>(B, L), mk<NEQ>(op::array::select(B, p),
                                                  v))) == bz::Result::UNSAT);
    CHECK(env.check(mk<AND>(mk<EQ>(B, L), mk<EQ>(op::array::select(B, p),
                                                 v))) == bz::Result::SAT);
    Expr c = env.boolc("c");
    Expr L0 = env.constLambda(a, env.num(0, 8));
    Expr L1 = env.constLambda(a, env.num(1, 8));
    CHECK(env.check(mk<AND>(mk<IMPL>(c, mk<EQ>(L0, L1)), c)) ==
          bz::Result::UNSAT);
    CHECK(env.check(mk<IMPL>(c, mk<EQ>(L0, L1))) == bz::Result::SAT);
    CHECK(isOpX<LAMBDA>(L0));
    CHECK(env.m.encode_term(L0).sort().is_fun());
  }
  SUBCASE("a bound variable shared by two lambdas") {
    // -- both bodies contain the same Expr (bvar 0); each must use its own
    // -- Bitwuzla variable
    Expr b = env.bvc("b", 8);
    Expr inc = env.lambda(a, mk<BADD>(a, env.num(1, 8)));
    Expr dbl = env.lambda(b, mk<BADD>(b, b));
    CHECK(env.valid(
        mk<AND>(mk<EQ>(bind::fapp(inc, env.num(3, 8)), env.num(4, 8)),
                mk<EQ>(bind::fapp(dbl, env.num(3, 8)), env.num(6, 8)))));
    CHECK(bind::body(inc)->left() == bind::body(dbl)->left());
  }
  SUBCASE("a lambda with two bound variables") {
    // -- de Bruijn index 0 is the last variable: (lambda (x y) (bvsub x y))
    Expr x = env.bvc("x", 8), y = env.bvc("y", 8);
    Expr S = bind::abs<LAMBDA>(std::array<Expr, 2>{x, y}, mk<BSUB>(x, y));
    CHECK(env.valid(
        mk<EQ>(bind::fapp(S, env.num(5, 8), env.num(3, 8)), env.num(2, 8))));
  }
  SUBCASE("binders inside lambdas") {
    // -- (lambda (x) (forall (y) (= (bvadd x y) (bvadd y x))))
    Expr x = env.bvc("x", 8), y = env.bvc("y", 8);
    Expr comm = mk<EQ>(mk<BADD>(x, y), mk<BADD>(y, x));
    Expr F = env.lambda(x, bind::abs<FORALL>(std::array<Expr, 1>{y}, comm));
    CHECK(env.valid(bind::fapp(F, env.num(5, 8))));
    // -- (forall (y) (bvule 0 y)) and (exists (y) (= y 5))
    CHECK(env.valid(
        bind::abs<FORALL>(std::array<Expr, 1>{y}, mk<BULE>(env.num(0, 8), y))));
    CHECK(env.valid(
        bind::abs<EXISTS>(std::array<Expr, 1>{y}, mk<EQ>(y, env.num(5, 8)))));
  }
}

TEST_CASE("bitwuzla.unsupported") {
  Env env;
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  Expr x = env.bvc("x", 8);
  auto rejects = [&](Expr e, Expr culprit) {
    try {
      env.m.encode_term(e);
    } catch (UnsupportedExpr &ex) {
      return !culprit || ex.expr() == culprit;
    }
    return false;
  };

  CHECK(rejects(i, nullptr));
  CHECK(rejects(bind::realConst(mkTerm<std::string>("r", env.efac)), nullptr));
  CHECK(rejects(mkTerm(expr::mpz_class(3UL), env.efac), nullptr));
  // -- integer operators, even on bit-vector arguments
  Expr leq = mk<LEQ>(x, x);
  CHECK(rejects(mk<AND>(mk<EQ>(x, x), leq), leq));
  Expr plus = mk<PLUS>(x, x);
  CHECK(rejects(mk<EQ>(plus, x), plus));
  // -- the culprit is the integer constant, not its sort
  CHECK(rejects(mk<EQ>(i, i), i));
  Expr b2i = mk<BV2INT>(x);
  CHECK(rejects(b2i, b2i));
  Expr rot = mk<BEXT_ROTATE_LEFT>(x, x);
  CHECK(rejects(rot, rot));
  Expr A = env.arrayc("A", 8, 8);
  Expr def = mk<ARRAY_DEFAULT>(A);
  CHECK(rejects(def, def));
  Expr st = strct::mk(x, x);
  CHECK(rejects(st, st));
  // -- nested lambdas: Bitwuzla would merge them into one function
  Expr y = env.bvc("y", 8);
  Expr nested = env.lambda(x, env.lambda(y, mk<BADD>(x, y)));
  CHECK(rejects(nested, nested));
  // -- a bound variable outside of any binder
  Expr b0 = bind::bvar(0, env.bvsort(8));
  CHECK(rejects(mk<EQ>(b0, x), b0));

  // -- the encoder still works after a rejection inside a binder
  CHECK(rejects(env.lambda(x, mk<EQ>(mk<BV2INT>(x), i)), nullptr));
  CHECK(env.valid(
      mk<EQ>(bind::fapp(env.lambda(x, x), env.num(3, 8)), env.num(3, 8))));
}

TEST_CASE("bitwuzla.deep expressions") {
  // -- the encoder uses an explicit stack: a chain deeper than the default
  // -- recursion limits of a naive encoder must not overflow
  Env env;
  Expr x = env.bvc("x", 32);
  Expr e = x;
  const unsigned depth = 100000;
  for (unsigned k = 0; k < depth; ++k)
    e = mk<BADD>(e, env.num(1, 32));
  CHECK(env.valid(mk<EQ>(e, mk<BADD>(x, env.num(depth, 32)))));
}

// -- the solver adapter, through the generic Solver interface

namespace {
Solver::expr_const_it_range litRange(const ExprVector &v) {
  return llvm::make_range(v.begin(), v.end());
}
} // namespace

TEST_CASE("bitwuzla.solver checkpoint") {
  // -- research-notes/durable/generic-solver-interface-contract.md
  Env env;
  bitwuzla_solver_impl bzla(env.efac);
  Solver &s = bzla;
  CHECK(s.get_kind() == seahorn::solver::SolverKind::BITWUZLA);
  Expr x = env.bvc("x", 8);

  // -- 1. x + 1 = 0 is sat with x = 255
  CHECK(s.add(mk<EQ>(mk<BADD>(x, env.num(1, 8)), env.num(0, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m = s.get_model();
  REQUIRE(m);
  Expr vx = m->eval(x, false);
  CHECK(vx == env.num(255, 8));
  CHECK(m->eval(x, true) == env.num(255, 8));
  CHECK(isOpX<TRUE>(m->eval(mk<BULT>(env.num(3, 8), x), false)));
  std::string printed;
  llvm::raw_string_ostream os(printed);
  os << *m;
  CHECK(os.str().find("x = #b11111111") != std::string::npos);

  // -- 2. push and x = 0 is unsat; the old model is stale
  s.push();
  CHECK(!m->eval(x, false));
  CHECK(s.add(mk<EQ>(x, env.num(0, 8))));
  CHECK(s.check() == SolverResult::UNSAT);
  CHECK(!s.get_model());

  // -- 3. pop is sat again
  s.pop();
  CHECK(s.check() == SolverResult::SAT);
  Solver::model_ref m2 = s.get_model();
  REQUIRE(m2);
  CHECK(m2->eval(x, false) == env.num(255, 8));

  // -- 4. reset empties the assertions and rejects the old model and core
  s.reset();
  CHECK(!m2->eval(x, false));
  ExprVector core;
  s.unsat_core(core);
  CHECK(core.empty());
  CHECK(s.check() == SolverResult::SAT);
  CHECK(s.add(mk<EQ>(x, env.num(7, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(s.get_model()->eval(x, false) == env.num(7, 8));
}

TEST_CASE("bitwuzla.solver unsat core") {
  Env env;
  bitwuzla_solver_impl bzla(env.efac);
  Solver &s = bzla;
  Expr x = env.bvc("x", 8), y = env.bvc("y", 8);
  ExprVector f = {mk<EQ>(x, env.num(1, 8)), mk<EQ>(x, env.num(2, 8)),
                  mk<EQ>(y, env.num(3, 8))};
  // -- activation literals as Path BMC's MUC builds them: the constraint is
  // -- inside the literal's name, so the core must hand back these Exprs
  ExprVector lits;
  for (Expr v : f) {
    Expr a = bind::boolConst(mk<ASM>(v));
    lits.push_back(a);
    CHECK(s.add(mk<IMPL>(a, v)));
  }

  REQUIRE(s.check_with_assumptions(litRange(lits)) == SolverResult::UNSAT);
  ExprVector core;
  s.unsat_core(core);
  // -- x = 1 and x = 2 are in every core, and every element is a literal
  auto has = [&](Expr a) {
    return std::find(core.begin(), core.end(), a) != core.end();
  };
  CHECK(has(lits[0]));
  CHECK(has(lits[1]));
  for (Expr c : core)
    CHECK(std::find(lits.begin(), lits.end(), c) != lits.end());

  // -- with a satisfiable subset, there is a model and no core
  ExprVector some = {lits[0], lits[2]};
  REQUIRE(s.check_with_assumptions(litRange(some)) == SolverResult::SAT);
  CHECK(s.get_model()->eval(x, false) == env.num(1, 8));
  ExprVector none;
  s.unsat_core(none);
  CHECK(none.empty());

  // -- a core is only for the check it came from
  REQUIRE(s.check_with_assumptions(litRange(lits)) == SolverResult::UNSAT);
  s.push();
  ExprVector stale;
  s.unsat_core(stale);
  CHECK(stale.empty());
  s.pop();

  // -- a plain check has no core
  CHECK(s.add(mk<EQ>(x, env.num(1, 8))));
  CHECK(s.add(mk<EQ>(x, env.num(2, 8))));
  REQUIRE(s.check() == SolverResult::UNSAT);
  ExprVector plain;
  s.unsat_core(plain);
  CHECK(plain.empty());
}

TEST_CASE("bitwuzla.solver unsupported input") {
  Env env;
  bitwuzla_solver_impl bzla(env.efac);
  Solver &s = bzla;
  Expr x = env.bvc("x", 8);
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  CHECK(s.add(mk<EQ>(x, env.num(1, 8))));

  // -- an assertion that cannot be encoded: add() says so, and since callers
  // -- (SolverBmc) ignore that, checks answer unknown, never sat or unsat
  s.push();
  CHECK_FALSE(s.add(mk<EQ>(i, i)));
  CHECK(s.add(mk<EQ>(x, env.num(2, 8)))); // unsat with the first one
  CHECK(s.check() == SolverResult::UNKNOWN);
  CHECK(s.check_with_assumptions(litRange(ExprVector{})) ==
        SolverResult::UNKNOWN);
  CHECK(!s.get_model());
  // -- popping the scope removes it
  s.pop();
  CHECK(s.check() == SolverResult::SAT);

  // -- at the bottom scope only reset() removes it
  CHECK_FALSE(s.add(mk<EQ>(i, i)));
  s.push();
  s.pop();
  CHECK(s.check() == SolverResult::UNKNOWN);
  s.reset();
  CHECK(s.check() == SolverResult::SAT);

  // -- an assumption that cannot be encoded affects only that check
  Expr bad = mk<EQ>(i, i);
  CHECK(s.check_with_assumptions(litRange(ExprVector{bad})) ==
        SolverResult::UNKNOWN);
  CHECK(s.check() == SolverResult::SAT);

  // -- the model of a term it cannot encode gives the term back
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(s.get_model()->eval(i, false) == i);

  // -- a non-Boolean assertion
  CHECK_FALSE(s.add(x));
  CHECK(s.check() == SolverResult::UNKNOWN);
}

TEST_CASE("bitwuzla.solver misuse is reported, not fatal") {
  Env env;
  bitwuzla_solver_impl bzla(env.efac);
  Solver &s = bzla;
  Expr x = env.bvc("x", 8);
  // -- no check yet: no model, no core
  CHECK(!s.get_model());
  ExprVector core;
  s.unsat_core(core);
  CHECK(core.empty());
  // -- pop without push
  s.pop();
  CHECK(s.add(mk<EQ>(x, env.num(4, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  // -- a model is stale after a new add, even if the answer would not change
  Solver::model_ref m = s.get_model();
  CHECK(s.add(mk<TRUE>(env.efac)));
  CHECK(!m->eval(x, false));
}

TEST_CASE("bitwuzla.solver smt-lib") {
  Env env;
  bitwuzla_solver_impl bzla(env.efac);
  Solver &s = bzla;
  Expr x = env.bvc("x", 8), a = env.boolc("a");
  CHECK(s.add(mk<IMPL>(a, mk<EQ>(x, env.num(5, 8)))));

  auto smt = [&]() {
    std::string str;
    llvm::raw_string_ostream os(str);
    s.to_smt_lib(os);
    return os.str();
  };
  std::string plain = smt();
  CHECK(plain.find("(declare-const x (_ BitVec 8))") != std::string::npos);
  CHECK(plain.find("(assert (=> a (= x #b00000101)))") != std::string::npos);
  CHECK(plain.find("(check-sat)") != std::string::npos);

  ExprVector lits = {a};
  REQUIRE(s.check_with_assumptions(litRange(lits)) == SolverResult::SAT);
  std::string assuming = smt();
  CHECK(assuming.find("(check-sat-assuming (a))") != std::string::npos);
  CHECK(assuming.find("(check-sat)") == std::string::npos);

  // -- a missing assertion is flagged in the output
  CHECK_FALSE(s.add(bind::intConst(mkTerm<std::string>("i", env.efac))));
  CHECK(smt().find("; WARNING: an assertion could not be encoded") !=
        std::string::npos);
}
#endif
