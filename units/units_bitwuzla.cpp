#ifdef WITH_BITWUZLA
/* Unit tests for the Bitwuzla encoder (marshal_bitwuzla) and solver */
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"

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

  bz::Result check(Expr e) {
    bz::Bitwuzla s(tm);
    s.assert_formula(m.encode_term(e));
    return s.check_sat();
  }
  bool valid(Expr e) { return check(mk<NEG>(e)) == bz::Result::UNSAT; }

  /// \p e cannot be encoded, and the error names \p culprit
  bool rejects(Expr e, Expr culprit) {
    try {
      m.encode_term(e);
    } catch (UnsupportedExpr &ex) {
      return ex.expr() == culprit;
    }
    return false;
  }
};

using BinOp = std::function<Expr(Expr, Expr)>;
template <typename Op> BinOp binop() {
  return [](Expr a, Expr b) { return mk<Op>(a, b); };
}

/// Z3's value of a variable-free \p t (through the existing EZ3 path)
Expr z3Value(EZ3 &z3, Expr t, Expr r) {
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
  CHECK_THROWS_AS(env.m.encode_sort(sort::intTy(env.efac)), UnsupportedExpr);
  CHECK_THROWS_AS(env.m.encode_sort(sort::realTy(env.efac)), UnsupportedExpr);
  // -- arrays come with memory (plan 1.6)
  CHECK_THROWS_AS(
      env.m.encode_sort(sort::arrayTy(env.bvsort(8), env.bvsort(8))),
      UnsupportedExpr);
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
  // -- constants of different sorts with the same name stay different
  CHECK(env.m.encode_term(env.bvc("x", 16)) != tx);
  CHECK(env.m.encode_term(env.boolc("b")).sort().is_bool());
}

TEST_CASE("bitwuzla.numerals") {
  Env env;
  // -- wider than 64 bits: 2^100 - 1
  Expr n100 = bv::bvnum(expr::mpz_class("1267650600228229401496703205375"), 128,
                        env.efac);
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
  CHECK(env.check(t) == bz::Result::SAT);
  CHECK(env.check(f) == bz::Result::UNSAT);
}

TEST_CASE("bitwuzla.bit-vector operators") {
  Env env;
  Expr x = env.bvc("x", 8);
  Expr one = env.num(1, 8), min = env.num(0x80, 8), ab = env.num(0xAB, 8);
  CHECK(env.valid(mk<EQ>(mk<BSUB>(mk<BADD>(x, one), one), x)));
  CHECK(env.valid(mk<EQ>(mk<BADD>(x, mk<BNEG>(x)), env.num(0, 8))));
  // -- n-ary add
  CHECK(env.valid(mk<EQ>(mknary<BADD>(ExprVector{x, one, x}),
                         mk<BADD>(x, mk<BADD>(x, one)))));
  // -- 0x80 is the largest unsigned and the smallest signed of these
  CHECK(env.valid(mk<BULT>(one, min)));
  CHECK(env.valid(mk<BULE>(one, min)));
  CHECK(env.valid(mk<BUGT>(min, one)));
  CHECK(env.valid(mk<BUGE>(min, one)));
  CHECK(env.valid(mk<BSLT>(min, one)));
  CHECK(env.valid(mk<BSLE>(min, one)));
  CHECK(env.valid(mk<BSGT>(one, min)));
  CHECK(env.valid(mk<BSGE>(one, min)));
  CHECK(env.valid(mk<BULE>(x, x)));
  CHECK(env.check(mk<BULT>(x, x)) == bz::Result::UNSAT);

  CHECK(env.valid(mk<EQ>(bv::extract(7, 4, ab), env.num(0xA, 4))));
  CHECK(env.valid(mk<EQ>(bv::extract(3, 0, ab), env.num(0xB, 4))));
  CHECK(env.valid(mk<EQ>(bv::sext(env.num(0x8, 4), 8), env.num(0xF8, 8))));
  CHECK(env.valid(mk<EQ>(bv::zext(env.num(0x8, 4), 8), env.num(0x08, 8))));
  // -- extending to the same width is the identity
  CHECK(env.valid(mk<EQ>(bv::zext(x, 8), x)));
  // -- the first argument of concat is the most significant
  CHECK(env.valid(mk<EQ>(mk<BCONCAT>(env.num(0xA, 4), env.num(0xB, 4)), ab)));
  CHECK(
      env.valid(mk<EQ>(mk<BCONCAT>(env.num(1, 1), env.num(0, 1), env.num(1, 1)),
                       env.num(5, 3))));
}

TEST_CASE("bitwuzla.bit-vector operators agree with z3") {
  Env env;
  EZ3 z3(env.efac);
  const unsigned w = 3;

  // -- division and remainder by zero are included: both follow SMT-LIB
  // -- names are std::string: doctest prints a const char * as a pointer
  std::vector<std::pair<std::string, BinOp>> ops = {
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
      {"extract", [](Expr a, Expr) { return bv::extract(2, 1, a); }},
      {"sext", [](Expr a, Expr) { return bv::sext(a, 5); }},
      {"zext", [](Expr a, Expr) { return bv::zext(a, 5); }},
  };

  bz::Bitwuzla bzla(env.tm);
  unsigned checked = 0, disagreements = 0;
  for (auto &op : ops) {
    for (long a = 0; a < (1 << w); ++a) {
      for (long b = 0; b < (1 << w); ++b) {
        Expr t = op.second(env.num(a, w), env.num(b, w));
        // -- the sort of the result, as Bitwuzla sees it
        bz::Sort s = env.m.encode_term(t).sort();
        Expr r = s.is_bool() ? env.boolc("r") : env.bvc("r", s.bv_size());
        Expr expected = z3Value(z3, t, r);

        bzla.push(1);
        bzla.assert_formula(env.m.encode_term(mk<NEQ>(t, expected)));
        bool agrees = bzla.check_sat() == bz::Result::UNSAT;
        bzla.pop(1);
        ++checked;
        if (!agrees) {
          ++disagreements;
          MESSAGE(op.first << " " << a << " " << b << ": z3 says "
                           << boost::lexical_cast<std::string>(*expected));
        }
      }
    }
  }
  CHECK(checked == ops.size() * 64);
  CHECK(disagreements == 0);
}

TEST_CASE("bitwuzla.overflow predicates agree with z3 and with arithmetic") {
  Env env;
  EZ3 z3(env.efac);

  // -- expected truth value from exact integer arithmetic, given a and b as
  // -- signed and as unsigned values, and the width
  struct Pred {
    std::string name;
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

TEST_CASE("bitwuzla.repeat, rotate and n-ary operators") {
  // -- Z3's marshal has no repeat or rotate, so these check exact values
  Env env;
  auto u = [&](unsigned n) { return mkTerm<unsigned>(n, env.efac); };
  Expr x81 = env.num(0x81, 8);
  CHECK(
      env.valid(mk<EQ>(mk<BREPEAT>(u(2), env.num(0xA, 4)), env.num(0xAA, 8))));
  CHECK(env.valid(mk<EQ>(mk<BROTATE_LEFT>(u(1), x81), env.num(0x03, 8))));
  CHECK(env.valid(mk<EQ>(mk<BROTATE_RIGHT>(u(1), x81), env.num(0xC0, 8))));
  // -- rotating by the width or more wraps around
  CHECK(env.valid(mk<EQ>(mk<BROTATE_LEFT>(u(8), x81), x81)));
  CHECK(env.valid(mk<EQ>(mk<BROTATE_LEFT>(u(9), x81), env.num(0x03, 8))));

  // -- n-ary forms of the associative operators
  Expr x = env.bvc("x", 8), y = env.bvc("y", 8), z = env.bvc("z", 8);
  CHECK(env.valid(
      mk<EQ>(mknary<BMUL>(ExprVector{x, y, z}), mk<BMUL>(x, mk<BMUL>(y, z)))));
  CHECK(env.valid(
      mk<EQ>(mknary<BAND>(ExprVector{x, y, z}), mk<BAND>(x, mk<BAND>(y, z)))));
  CHECK(env.valid(
      mk<EQ>(mknary<BOR>(ExprVector{x, y, z}), mk<BOR>(x, mk<BOR>(y, z)))));
  CHECK(env.valid(
      mk<EQ>(mknary<BXOR>(ExprVector{x, y, z}), mk<BXOR>(x, mk<BXOR>(y, z)))));
  // -- the others take two arguments in Bitwuzla
  Expr sub3 = mknary<BSUB>(ExprVector{x, y, z});
  CHECK(env.rejects(mk<EQ>(sub3, x), sub3));
}

TEST_CASE("bitwuzla.unsupported") {
  Env env;
  Expr x = env.bvc("x", 8);
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));

  // -- the error names the unsupported operator, not one of its arguments
  Expr i2b = mk<INT2BV>(mkTerm<unsigned>(8, env.efac), i);
  CHECK(env.rejects(mk<AND>(mk<EQ>(x, x), mk<BULT>(i2b, x)), i2b));
  Expr b2i = mk<BV2INT>(x);
  CHECK(env.rejects(mk<EQ>(b2i, b2i), b2i));
  Expr rot = mk<BEXT_ROTATE_LEFT>(x, env.num(1, 8));
  CHECK(env.rejects(mk<EQ>(rot, x), rot));
  Expr leq = mk<LEQ>(x, x);
  CHECK(env.rejects(mk<OR>(leq, mk<EQ>(x, x)), leq));
  // -- constants of unsupported sorts: integers, arrays (plan 1.6)
  CHECK(env.rejects(mk<EQ>(i, i), i));
  Expr A = bind::mkConst(mkTerm<std::string>("A", env.efac),
                         sort::arrayTy(env.bvsort(8), env.bvsort(8)));
  Expr sel = op::array::select(A, x);
  CHECK(env.rejects(mk<EQ>(sel, x), sel));
  // -- uninterpreted functions
  Expr f = bind::fdecl(mkTerm<std::string>("f", env.efac),
                       ExprVector{env.bvsort(8), env.bvsort(8)});
  Expr fx = bind::fapp(f, x);
  CHECK(env.rejects(mk<EQ>(fx, x), fx));
  // -- a bound variable outside of any binder
  Expr b0 = bind::bvar(0, env.bvsort(8));
  CHECK(env.rejects(mk<EQ>(b0, x), b0));

  // -- the encoder still works after a rejection
  CHECK(env.valid(mk<EQ>(mk<BADD>(x, env.num(0, 8)), x)));

  // -- the message stays short for a large DAG: printed as a tree, this one
  // -- has 2^64 nodes (memset.symbolic.unaligned in test/opsem hung on that)
  Expr big = x;
  for (unsigned k = 0; k < 64; ++k)
    big = mk<BADD>(big, big);
  Expr bigrot = mk<BEXT_ROTATE_LEFT>(big, x);
  try {
    env.m.encode_term(mk<EQ>(bigrot, x));
    FAIL("rotation by a term is not supported");
  } catch (UnsupportedExpr &ex) {
    CHECK(ex.expr() == bigrot);
    CHECK(std::string(ex.what()).find("bvextrotleft(bvadd(...), x)") !=
          std::string::npos);
  }
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

TEST_CASE("bitwuzla.solver") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  CHECK(s.get_kind() == seahorn::solver::SolverKind::BITWUZLA);
  Expr x = env.bvc("x", 8);

  // -- x + 1 = 0 is sat (with x = 255); adding x = 0 makes it unsat
  CHECK(s.add(mk<EQ>(mk<BADD>(x, env.num(1, 8)), env.num(0, 8))));
  CHECK(s.check() == SolverResult::SAT);
  CHECK(s.add(mk<EQ>(x, env.num(0, 8))));
  CHECK(s.check() == SolverResult::UNSAT);

  // -- reset removes every assertion
  s.reset();
  CHECK(s.check() == SolverResult::SAT);
  CHECK(s.add(mk<EQ>(x, env.num(7, 8))));
  CHECK(s.check() == SolverResult::SAT);
  CHECK(s.add(mk<BULT>(x, env.num(7, 8))));
  CHECK(s.check() == SolverResult::UNSAT);
}

TEST_CASE("bitwuzla.solver unsupported input") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr x = env.bvc("x", 8);
  CHECK(s.add(mk<EQ>(x, env.num(1, 8))));

  // -- an assertion that cannot be encoded: add() says so, and since callers
  // -- (SolverBmc) ignore that, checks answer unknown, never sat or unsat
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  CHECK_FALSE(s.add(mk<EQ>(mk<BV2INT>(x), i)));
  CHECK(s.check() == SolverResult::UNKNOWN);
  CHECK(s.add(mk<EQ>(x, env.num(2, 8)))); // unsat with the first one
  CHECK(s.check() == SolverResult::UNKNOWN);

  // -- reset removes it
  s.reset();
  CHECK(s.check() == SolverResult::SAT);

  // -- a non-Boolean assertion
  CHECK_FALSE(s.add(x));
  CHECK(s.check() == SolverResult::UNKNOWN);
  s.reset();
  CHECK(s.add(mk<EQ>(x, env.num(2, 8))));
  CHECK(s.check() == SolverResult::SAT);
}

#endif
