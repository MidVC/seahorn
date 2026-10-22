#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/lexical_cast.hpp"

#include <algorithm>
#include <gmp.h>

using namespace expr;
using bitwuzla::Kind;
using bitwuzla::Sort;
using bitwuzla::Term;

namespace seahorn {
namespace solver {

static std::string describe(Expr e, const std::string &reason) {
  std::string str;
  llvm::raw_string_ostream os(str);
  os << *e;
  os.flush();
  // -- the offending Expr can be a large DAG
  const size_t max_len = 300;
  if (str.size() > max_len)
    str = str.substr(0, max_len) + " ...";
  return reason + ": " + str;
}

UnsupportedExpr::UnsupportedExpr(Expr e, const std::string &reason)
    : std::runtime_error(describe(e, reason)), m_expr(e) {}

static std::string get_name(Expr e) {
  Expr fname;
  if (bind::isFapp(e)) {
    // name of the app
    fname = bind::fname(e);
    // name of the fdecl
    fname = bind::fname(fname);
  } else if (bind::isFdecl(e)) {
    // name of the fdecl
    fname = bind::fname(e);
  } else {
    fname = e;
  }

  if (isOpX<STRING>(fname))
    return getTerm<std::string>(fname);
  return boost::lexical_cast<std::string>(*fname);
}

static bool isBinder(Expr e) {
  return isOpX<LAMBDA>(e) || isOpX<FORALL>(e) || isOpX<EXISTS>(e);
}

/// Exprs that are encoded without encoding any children first
static bool isLeaf(Expr e) {
  return e->arity() == 0 || isOpX<BIND>(e) ||
         (bind::isFapp(e) && e->arity() == 1);
}

namespace {
/// Thrown by the term builders below; mkNode() turns it into UnsupportedExpr
struct Rejected : public std::runtime_error {
  using std::runtime_error::runtime_error;
};

void requireArity(const std::vector<Term> &args, size_t n) {
  if (args.size() != n)
    throw Rejected("expected " + std::to_string(n) + " arguments, got " +
                   std::to_string(args.size()));
}
} // namespace

Sort marshal_bitwuzla::encode_sort(Expr s) {
  if (isOpX<BOOL_TY>(s))
    return m_tm.mk_bool_sort();
  if (isOpX<BVSORT>(s))
    return m_tm.mk_bv_sort(bv::width(s));
  if (isOpX<ARRAY_TY>(s))
    return m_tm.mk_array_sort(encode_sort(sort::arrayIndexTy(s)),
                              encode_sort(sort::arrayValTy(s)));
  if (isOpX<FUNCTIONAL_TY>(s)) {
    std::vector<Sort> domain;
    for (unsigned i = 0, sz = s->arity() - 1; i < sz; ++i)
      domain.push_back(encode_sort(s->arg(i)));
    return m_tm.mk_fun_sort(domain, encode_sort(s->last()));
  }
  if (isOpX<INT_TY>(s) || isOpX<REAL_TY>(s))
    throw UnsupportedExpr(s, "Bitwuzla has no integer or real sort");
  if (isOpX<STRUCT_TY>(s))
    throw UnsupportedExpr(s, "struct sorts are not supported yet");
  throw UnsupportedExpr(s, "unsupported sort");
}

bool marshal_bitwuzla::lookup(Expr e, Encoded &out) const {
  auto it = m_cache.find(e);
  if (it != m_cache.end()) {
    out = {it->second, 0};
    return true;
  }
  // -- an open term means something else under another binder, so only
  // -- the innermost scope is searched
  if (!m_scopes.empty()) {
    auto &cache = m_scopes.back().cache;
    auto jt = cache.find(e);
    if (jt != cache.end()) {
      out = jt->second;
      return true;
    }
  }
  return false;
}

void marshal_bitwuzla::store(Expr e, const Encoded &enc) {
  if (enc.fv == 0)
    m_cache.insert({e, enc.term});
  else if (!m_scopes.empty())
    m_scopes.back().cache.insert({e, enc});
  else
    throw UnsupportedExpr(e, "term has a free bound variable");
}

std::vector<unsigned> marshal_bitwuzla::termArgs(Expr e) {
  unsigned first = 0, last = e->arity();
  if (isOpX<BEXTRACT>(e))
    first = 2; // (extract high low bv)
  else if (isOpX<BSEXT>(e) || isOpX<BZEXT>(e))
    last = 1; // (sext bv sort)
  else if (isOpX<BREPEAT>(e) || isOpX<BROTATE_LEFT>(e) ||
           isOpX<BROTATE_RIGHT>(e) || isOpX<CONST_ARRAY>(e))
    first = 1; // (repeat n bv), (rotate n bv), (const-array sort v)
  else if (bind::isFapp(e) && bind::isFdecl(bind::fname(e)))
    first = 1; // (fapp fdecl args...)

  std::vector<unsigned> res;
  for (unsigned i = first; i < last; ++i)
    res.push_back(i);
  return res;
}

Term marshal_bitwuzla::declare(Expr fdecl) {
  auto it = m_cache.find(fdecl);
  if (it != m_cache.end())
    return it->second;

  Sort sort = encode_sort(bind::rangeTy(fdecl));
  if (bind::domainSz(fdecl) > 0) {
    std::vector<Sort> domain;
    for (size_t i = 0, sz = bind::domainSz(fdecl); i < sz; ++i)
      domain.push_back(encode_sort(bind::domainTy(fdecl, i)));
    sort = m_tm.mk_fun_sort(domain, sort);
  }

  // -- identity comes from the cache: two declarations may print the same
  Term res = m_tm.mk_const(sort, get_name(fdecl));
  m_cache.insert({fdecl, res});
  m_decls.push_back({fdecl, res});
  return res;
}

marshal_bitwuzla::Encoded marshal_bitwuzla::mkLeaf(Expr e) {
  if (isOpX<TRUE>(e))
    return {m_tm.mk_true(), 0};
  if (isOpX<FALSE>(e))
    return {m_tm.mk_false(), 0};

  if (bv::is_bvnum(e)) {
    unsigned width = bv::width(e->arg(1));
    const expr::mpz_class &num = getTerm<expr::mpz_class>(e->arg(0));
    // -- the decimal string keeps values wider than 64 bits. Bitwuzla rejects
    // -- values outside of [0, 2^width), so reduce modulo 2^width first.
    mpz_t r;
    mpz_init(r);
    mpz_fdiv_r_2exp(r, num.get_mpz_t(), width);
    std::string snum = expr::mpz_class(r).to_string();
    mpz_clear(r);
    return {m_tm.mk_bv_value(m_tm.mk_bv_sort(width), snum, 10), 0};
  }

  if (bind::isBVar(e)) {
    // -- de Bruijn index, as in Z3: 0 is the last variable of the innermost
    // -- binder
    unsigned idx = bind::bvarId(e);
    unsigned rest = idx;
    for (auto it = m_scopes.rbegin(), end = m_scopes.rend(); it != end; ++it) {
      unsigned k = it->vars.size();
      if (rest < k) {
        Term v = it->vars[k - 1 - rest];
        if (v.sort() != encode_sort(bind::type(e)))
          throw UnsupportedExpr(
              e, "bound variable sort differs from its binder's declaration");
        return {v, idx + 1};
      }
      rest -= k;
    }
    throw UnsupportedExpr(e, "bound variable outside of its binder");
  }

  if (bind::isFapp(e) && bind::isFdecl(bind::fname(e))) {
    try {
      return {declare(bind::fname(e)), 0};
    } catch (UnsupportedExpr &ex) {
      // -- report the constant rather than its sort
      throw UnsupportedExpr(e, ex.what());
    }
  }

  if (isOpX<MPZ>(e) || isOpX<MPQ>(e) || isOpX<UINT>(e))
    throw UnsupportedExpr(e, "Bitwuzla has no integer or real numerals");
  throw UnsupportedExpr(e, "unsupported term");
}

void marshal_bitwuzla::enterBinder(Expr e) {
  Scope scope;
  for (unsigned i = 0, sz = bind::numBound(e); i < sz; ++i)
    scope.vars.push_back(m_tm.mk_var(encode_sort(bind::boundSort(e, i)),
                                     get_name(bind::boundName(e, i))));
  m_scopes.push_back(std::move(scope));
}

marshal_bitwuzla::Encoded marshal_bitwuzla::leaveBinder(Expr e) {
  Encoded body;
  bool found = lookup(bind::body(e), body);
  assert(found && "binder body is not encoded");
  (void)found;

  std::vector<Term> args = m_scopes.back().vars;
  unsigned num_bound = args.size();
  m_scopes.pop_back();

  // -- Bitwuzla merges (lambda x (lambda y b)) into one function of x and y,
  // -- which no longer matches how SeaHorn applies it
  if (isOpX<LAMBDA>(e) && body.term.sort().is_fun())
    throw UnsupportedExpr(e, "lambda whose body is a function");

  args.push_back(body.term);
  Kind kind = isOpX<LAMBDA>(e)   ? Kind::LAMBDA
              : isOpX<FORALL>(e) ? Kind::FORALL
                                 : Kind::EXISTS;
  Term res;
  try {
    res = m_tm.mk_term(kind, args);
  } catch (bitwuzla::Exception &ex) {
    throw UnsupportedExpr(e, "Bitwuzla rejects the encoding: " + ex.msg());
  }
  return {res, body.fv > num_bound ? body.fv - num_bound : 0};
}

/// Applies \p f to \p args: APPLY for a function, ARRAY_SELECT for an array.
/// SeaHorn uses both for both (lambdas are arrays in Z3).
Term marshal_bitwuzla::mkApp(Term f, const std::vector<Term> &args) {
  if (f.sort().is_fun()) {
    std::vector<Term> v{f};
    v.insert(v.end(), args.begin(), args.end());
    return m_tm.mk_term(Kind::APPLY, v);
  }
  if (f.sort().is_array()) {
    requireArity(args, 1);
    return m_tm.mk_term(Kind::ARRAY_SELECT, {f, args[0]});
  }
  throw Rejected("applying a term that is neither a function nor an array");
}

/// Equality. Bitwuzla does not support equality between functions, so for a
/// function (a lambda) the equality is stated pointwise with a quantifier:
/// (forall xs (= (a xs) (b xs))). This is the extensional equality that Z3
/// uses for arrays and lambdas.
Term marshal_bitwuzla::mkEq(Term a, Term b) {
  if (!a.sort().is_fun() && !b.sort().is_fun())
    return m_tm.mk_term(Kind::EQUAL, {a, b});

  LOG("bitwuzla", WARN << "equality between functions encoded with a "
                          "quantifier\n";);
  std::vector<Term> vars;
  for (const Sort &s : (a.sort().is_fun() ? a : b).sort().fun_domain())
    vars.push_back(m_tm.mk_var(s));
  Term body = m_tm.mk_term(Kind::EQUAL, {mkApp(a, vars), mkApp(b, vars)});
  vars.push_back(body);
  return m_tm.mk_term(Kind::FORALL, vars);
}

/// If-then-else. Bitwuzla 0.9.1 aborts in check_sat() on an ITE between
/// lambdas, so for functions the ITE is moved inside a lambda:
/// (lambda xs (ite c (t xs) (e xs))). SeaHorn's bind::lite() does the same.
Term marshal_bitwuzla::mkIte(Term c, Term t, Term e) {
  if (!t.sort().is_fun() && !e.sort().is_fun())
    return m_tm.mk_term(Kind::ITE, {c, t, e});

  std::vector<Term> vars;
  for (const Sort &s : (t.sort().is_fun() ? t : e).sort().fun_domain())
    vars.push_back(m_tm.mk_var(s));
  Term body = m_tm.mk_term(Kind::ITE, {c, mkApp(t, vars), mkApp(e, vars)});
  vars.push_back(body);
  return m_tm.mk_term(Kind::LAMBDA, vars);
}

/// Array store. On a function, it becomes (lambda x (ite (= x i) v (a x))).
Term marshal_bitwuzla::mkStore(Term a, Term i, Term v) {
  if (a.sort().is_array())
    return m_tm.mk_term(Kind::ARRAY_STORE, {a, i, v});
  if (a.sort().is_fun() && a.sort().fun_domain().size() == 1) {
    Term x = m_tm.mk_var(a.sort().fun_domain()[0]);
    Term body = m_tm.mk_term(Kind::ITE, {m_tm.mk_term(Kind::EQUAL, {x, i}), v,
                                         m_tm.mk_term(Kind::APPLY, {a, x})});
    return m_tm.mk_term(Kind::LAMBDA, {x, body});
  }
  throw Rejected("store into a term that is not an array");
}

Term marshal_bitwuzla::mkBv(Expr e, const std::vector<Term> &a) {
  auto nary = [&](Kind k) { return a.size() == 1 ? a[0] : m_tm.mk_term(k, a); };
  auto unary = [&](Kind k) {
    requireArity(a, 1);
    return m_tm.mk_term(k, a);
  };
  auto binary = [&](Kind k) {
    requireArity(a, 2);
    return m_tm.mk_term(k, a);
  };
  auto lnot = [&](Term t) { return m_tm.mk_term(Kind::NOT, {t}); };
  auto land = [&](Term t, Term u) { return m_tm.mk_term(Kind::AND, {t, u}); };
  // -- sign bit set
  auto neg = [&](Term t) {
    return m_tm.mk_term(Kind::BV_SLT, {t, m_tm.mk_bv_zero(t.sort())});
  };
  auto uindex = [&](unsigned i) -> uint64_t {
    if (!isOpX<UINT>(e->arg(i)))
      throw Rejected("expected an unsigned numeral as index");
    return getTerm<unsigned>(e->arg(i));
  };

  switch (llvm::cast<BvOp>(e->op()).m_kind) {
  case BvOpKind::BNOT:
    return unary(Kind::BV_NOT);
  case BvOpKind::BNEG:
    return unary(Kind::BV_NEG);
  // -- the result is 1 bit wide, as in Z3
  case BvOpKind::BREDAND:
    return unary(Kind::BV_REDAND);
  case BvOpKind::BREDOR:
    return unary(Kind::BV_REDOR);
  // -- associative: Bitwuzla takes any number of arguments
  case BvOpKind::BAND:
    return nary(Kind::BV_AND);
  case BvOpKind::BOR:
    return nary(Kind::BV_OR);
  case BvOpKind::BXOR:
    return nary(Kind::BV_XOR);
  case BvOpKind::BADD:
    return nary(Kind::BV_ADD);
  case BvOpKind::BMUL:
    return nary(Kind::BV_MUL);
  // -- the first argument is the most significant, in both
  case BvOpKind::BCONCAT:
    return nary(Kind::BV_CONCAT);
  case BvOpKind::BNAND:
    return binary(Kind::BV_NAND);
  case BvOpKind::BNOR:
    return binary(Kind::BV_NOR);
  case BvOpKind::BXNOR:
    return binary(Kind::BV_XNOR);
  case BvOpKind::BSUB:
    return binary(Kind::BV_SUB);
  case BvOpKind::BUDIV:
    return binary(Kind::BV_UDIV);
  case BvOpKind::BSDIV:
    return binary(Kind::BV_SDIV);
  case BvOpKind::BUREM:
    return binary(Kind::BV_UREM);
  case BvOpKind::BSREM:
    return binary(Kind::BV_SREM);
  case BvOpKind::BSMOD:
    return binary(Kind::BV_SMOD);
  case BvOpKind::BSHL:
    return binary(Kind::BV_SHL);
  case BvOpKind::BLSHR:
    return binary(Kind::BV_SHR);
  case BvOpKind::BASHR:
    return binary(Kind::BV_ASHR);
  case BvOpKind::BULT:
    return binary(Kind::BV_ULT);
  case BvOpKind::BSLT:
    return binary(Kind::BV_SLT);
  case BvOpKind::BULE:
    return binary(Kind::BV_ULE);
  case BvOpKind::BSLE:
    return binary(Kind::BV_SLE);
  case BvOpKind::BUGE:
    return binary(Kind::BV_UGE);
  case BvOpKind::BSGE:
    return binary(Kind::BV_SGE);
  case BvOpKind::BUGT:
    return binary(Kind::BV_UGT);
  case BvOpKind::BSGT:
    return binary(Kind::BV_SGT);
  case BvOpKind::BEXTRACT:
    requireArity(a, 1);
    return m_tm.mk_term(Kind::BV_EXTRACT, a, {bv::high(e), bv::low(e)});
  case BvOpKind::BSEXT:
  case BvOpKind::BZEXT: {
    // -- SeaHorn stores the target sort, Bitwuzla wants the extension amount
    requireArity(a, 1);
    uint64_t in_width = a[0].sort().bv_size();
    uint64_t out_width = bv::width(e->arg(1));
    if (out_width < in_width)
      throw Rejected("extension to a narrower sort");
    if (out_width == in_width)
      return a[0];
    Kind k = isOpX<BSEXT>(e) ? Kind::BV_SIGN_EXTEND : Kind::BV_ZERO_EXTEND;
    return m_tm.mk_term(k, a, {out_width - in_width});
  }
  case BvOpKind::BREPEAT:
    requireArity(a, 1);
    return m_tm.mk_term(Kind::BV_REPEAT, a, {uindex(0)});
  case BvOpKind::BROTATE_LEFT:
    requireArity(a, 1);
    return m_tm.mk_term(Kind::BV_ROLI, a, {uindex(0)});
  case BvOpKind::BROTATE_RIGHT:
    requireArity(a, 1);
    return m_tm.mk_term(Kind::BV_RORI, a, {uindex(0)});

  // -- Z3 splits signed overflow by direction; Bitwuzla's *_OVERFLOW kinds
  // -- are true when the exact result is out of range in either direction.
  // -- An out-of-range signed sum or difference is too large iff the first
  // -- argument is non-negative; a product iff the signs agree.
  case BvOpKind::UADD_NO_OVERFLOW:
    requireArity(a, 2);
    return lnot(m_tm.mk_term(Kind::BV_UADD_OVERFLOW, a));
  case BvOpKind::USUB_NO_UNDERFLOW:
    requireArity(a, 2);
    return lnot(m_tm.mk_term(Kind::BV_USUB_OVERFLOW, a));
  case BvOpKind::UMUL_NO_OVERFLOW:
    requireArity(a, 2);
    return lnot(m_tm.mk_term(Kind::BV_UMUL_OVERFLOW, a));
  case BvOpKind::SADD_NO_OVERFLOW:
    requireArity(a, 2);
    return lnot(land(m_tm.mk_term(Kind::BV_SADD_OVERFLOW, a), lnot(neg(a[0]))));
  case BvOpKind::SADD_NO_UNDERFLOW:
    requireArity(a, 2);
    return lnot(land(m_tm.mk_term(Kind::BV_SADD_OVERFLOW, a), neg(a[0])));
  case BvOpKind::SSUB_NO_OVERFLOW:
    requireArity(a, 2);
    return lnot(land(m_tm.mk_term(Kind::BV_SSUB_OVERFLOW, a), lnot(neg(a[0]))));
  case BvOpKind::SSUB_NO_UNDERFLOW:
    requireArity(a, 2);
    return lnot(land(m_tm.mk_term(Kind::BV_SSUB_OVERFLOW, a), neg(a[0])));
  case BvOpKind::SMUL_NO_OVERFLOW:
    requireArity(a, 2);
    return lnot(land(m_tm.mk_term(Kind::BV_SMUL_OVERFLOW, a),
                     m_tm.mk_term(Kind::EQUAL, {neg(a[0]), neg(a[1])})));
  case BvOpKind::SMUL_NO_UNDERFLOW:
    requireArity(a, 2);
    return lnot(land(m_tm.mk_term(Kind::BV_SMUL_OVERFLOW, a),
                     m_tm.mk_term(Kind::DISTINCT, {neg(a[0]), neg(a[1])})));

  case BvOpKind::BEXT_ROTATE_LEFT:
  case BvOpKind::BEXT_ROTATE_RIGHT:
    throw Rejected("rotation by a term is not supported");
  case BvOpKind::INT2BV:
  case BvOpKind::BV2INT:
    throw Rejected("Bitwuzla has no integers");
  }
  throw Rejected("unsupported bit-vector operator");
}

Term marshal_bitwuzla::mkNode(Expr e, const std::vector<Term> &a) {
  auto nary = [&](Kind k) { return a.size() == 1 ? a[0] : m_tm.mk_term(k, a); };
  auto binary = [&](Kind k) {
    requireArity(a, 2);
    return m_tm.mk_term(k, a);
  };

  try {
    switch (e->op().getFamilyId()) {
    case OpFamilyId::BoolOp:
      switch (llvm::cast<BoolOp>(e->op()).m_kind) {
      case BoolOpKind::AND:
        return nary(Kind::AND);
      case BoolOpKind::OR:
        return nary(Kind::OR);
      case BoolOpKind::XOR:
        return nary(Kind::XOR);
      case BoolOpKind::NEG:
        requireArity(a, 1);
        return m_tm.mk_term(Kind::NOT, a);
      case BoolOpKind::IMPL:
        return binary(Kind::IMPLIES);
      case BoolOpKind::IFF:
        return binary(Kind::IFF);
      case BoolOpKind::ITE:
        requireArity(a, 3);
        return mkIte(a[0], a[1], a[2]);
      default:
        break;
      }
      break;
    case OpFamilyId::CompareOp:
      switch (llvm::cast<CompareOp>(e->op()).m_kind) {
      case CompareOpKind::EQ:
        requireArity(a, 2);
        return mkEq(a[0], a[1]);
      case CompareOpKind::NEQ:
        requireArity(a, 2);
        return m_tm.mk_term(Kind::NOT, {mkEq(a[0], a[1])});
      default:
        throw Rejected("Bitwuzla has no integer or real comparisons");
      }
    case OpFamilyId::NumericOp:
      throw Rejected("Bitwuzla has no integer or real arithmetic");
    case OpFamilyId::ArrayOp:
      switch (llvm::cast<ArrayOp>(e->op()).m_kind) {
      case ArrayOpKind::SELECT:
        requireArity(a, 2);
        return mkApp(a[0], {a[1]});
      case ArrayOpKind::STORE:
        requireArity(a, 3);
        return mkStore(a[0], a[1], a[2]);
      case ArrayOpKind::CONST_ARRAY: {
        // -- (const-array index-sort v)
        requireArity(a, 1);
        Sort sort = m_tm.mk_array_sort(encode_sort(e->arg(0)), a[0].sort());
        return m_tm.mk_const_array(sort, a[0]);
      }
      default:
        throw Rejected("unsupported array operator");
      }
    case OpFamilyId::BindOp:
      if (bind::isFapp(e)) {
        if (bind::isFdecl(bind::fname(e)))
          return mkApp(declare(bind::fname(e)), a);
        // -- application of a lambda (or of an array)
        std::vector<Term> args(a.begin() + 1, a.end());
        return mkApp(a[0], args);
      }
      break;
    case OpFamilyId::BvOp:
      return mkBv(e, a);
    case OpFamilyId::StructOp:
      throw Rejected("structs are not supported yet");
    case OpFamilyId::FiniteMapOp:
      throw Rejected("finite maps are not supported");
    default:
      break;
    }
  } catch (bitwuzla::Exception &ex) {
    throw UnsupportedExpr(e, "Bitwuzla rejects the encoding: " + ex.msg());
  } catch (Rejected &ex) {
    throw UnsupportedExpr(e, ex.what());
  }
  throw UnsupportedExpr(e, "unsupported operator");
}

Term marshal_bitwuzla::encode_term(Expr root) {
  assert(m_scopes.empty());

  struct Frame {
    Expr e;
    bool expanded;
  };
  // -- an explicit stack: memory expressions can be very deep
  std::vector<Frame> todo{{root, false}};
  std::vector<Term> args;

  try {
    while (!todo.empty()) {
      Expr e = todo.back().e;
      Encoded enc;

      if (!todo.back().expanded) {
        if (lookup(e, enc)) {
          todo.pop_back();
          continue;
        }
        if (isBinder(e)) {
          todo.back().expanded = true;
          enterBinder(e);
          todo.push_back({bind::body(e), false});
          continue;
        }
        if (isLeaf(e)) {
          store(e, mkLeaf(e));
          todo.pop_back();
          continue;
        }
        todo.back().expanded = true;
        bool pending = false;
        for (unsigned i : termArgs(e)) {
          Encoded arg;
          if (!lookup(e->arg(i), arg)) {
            todo.push_back({e->arg(i), false});
            pending = true;
          }
        }
        if (pending)
          continue;
      } else if (isBinder(e)) {
        // -- the body is encoded and the binder's scope is innermost
        todo.pop_back();
        store(e, leaveBinder(e));
        continue;
      }

      // -- all term arguments are encoded
      args.clear();
      unsigned fv = 0;
      for (unsigned i : termArgs(e)) {
        Encoded arg;
        bool found = lookup(e->arg(i), arg);
        assert(found && "argument is not encoded");
        (void)found;
        args.push_back(arg.term);
        fv = std::max(fv, arg.fv);
      }
      Term res = mkNode(e, args);
      todo.pop_back();
      store(e, {res, fv});
    }
  } catch (...) {
    m_scopes.clear();
    throw;
  }

  Encoded res;
  bool found = lookup(root, res);
  assert(found && res.fv == 0);
  (void)found;
  return res.term;
}

} // namespace solver
} // namespace seahorn

#endif
