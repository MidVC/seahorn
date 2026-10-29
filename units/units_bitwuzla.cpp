#ifdef WITH_BITWUZLA
/* Unit tests for the Bitwuzla encoder (marshal_bitwuzla) and solver */
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"

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

TEST_CASE("bitwuzla.unsupported") {
  Env env;
  Expr x = env.bvc("x", 8);

  // -- the error names the unsupported operator, not one of its arguments
  Expr mul = mk<BMUL>(x, x);
  CHECK(env.rejects(mk<AND>(mk<EQ>(x, x), mk<BULT>(mul, x)), mul));
  Expr leq = mk<LEQ>(x, x);
  CHECK(env.rejects(mk<OR>(leq, mk<EQ>(x, x)), leq));
  // -- constants of unsupported sorts: integers, arrays (plan 1.6)
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
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
  Expr bigmul = mk<BMUL>(big, x);
  try {
    env.m.encode_term(mk<EQ>(bigmul, x));
    FAIL("bvmul is not supported");
  } catch (UnsupportedExpr &ex) {
    CHECK(ex.expr() == bigmul);
    CHECK(std::string(ex.what()).find("bvmul(bvadd(...), x)") !=
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
  CHECK_FALSE(s.add(mk<EQ>(mk<BMUL>(x, x), env.num(1, 8))));
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
