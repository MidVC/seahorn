#ifdef WITH_BITWUZLA
#pragma once

#include "bitwuzla/cpp/bitwuzla.h"
#include "seahorn/Expr/Expr.hh"

#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace seahorn {
namespace solver {

/// \brief Thrown by marshal_bitwuzla for an Expr that has no Bitwuzla
/// encoding (e.g., integer or real arithmetic, structs, finite maps)
class UnsupportedExpr : public std::runtime_error {
  expr::Expr m_expr;

public:
  UnsupportedExpr(expr::Expr e, const std::string &reason);
  /// \brief The offending sub-expression
  expr::Expr expr() const { return m_expr; }
};

/// \brief Encodes Exprs as Bitwuzla terms of a given TermManager
///
/// Results are cached, so encoding the same Expr twice returns the same
/// term, and every SeaHorn constant becomes exactly one Bitwuzla constant.
///
/// Bitwuzla reports errors with C++ exceptions, so the files that use this
/// class are compiled with -fexceptions. No exception may escape into the
/// rest of SeaHorn, which may be compiled without them: callers catch
/// UnsupportedExpr (and bitwuzla::Exception) at their API boundary.
class marshal_bitwuzla {
public:
  explicit marshal_bitwuzla(bitwuzla::TermManager &tm) : m_tm(tm) {}

  /// \brief Encodes a closed term. Throws UnsupportedExpr.
  bitwuzla::Term encode_term(expr::Expr e);

  /// \brief Encodes a sort expression. Throws UnsupportedExpr.
  bitwuzla::Sort encode_sort(expr::Expr s);

  /// \brief Constants and uninterpreted functions created so far, in order
  const std::vector<std::pair<expr::Expr, bitwuzla::Term>> &decls() const {
    return m_decls;
  }

  bitwuzla::TermManager &tm() { return m_tm; }

private:
  /// A term together with one more than the largest de Bruijn index that is
  /// free in its Expr (0 means the Expr is closed)
  struct Encoded {
    bitwuzla::Term term;
    unsigned fv;
  };

  /// The variables of one binder that is being encoded, and the terms built
  /// under it that refer to bound variables. Such terms are valid only under
  /// this binder, so they are never cached globally.
  struct Scope {
    std::vector<bitwuzla::Term> vars;
    std::unordered_map<expr::Expr, Encoded> cache;
  };

  bool lookup(expr::Expr e, Encoded &out) const;
  void store(expr::Expr e, const Encoded &enc);

  /// \brief Indices of the children of \p e that are terms (not sorts,
  /// declarations or numeric indices)
  static std::vector<unsigned> termArgs(expr::Expr e);

  void enterBinder(expr::Expr e);
  Encoded leaveBinder(expr::Expr e);
  Encoded mkLeaf(expr::Expr e);
  bitwuzla::Term mkNode(expr::Expr e, const std::vector<bitwuzla::Term> &args);
  bitwuzla::Term mkBv(expr::Expr e, const std::vector<bitwuzla::Term> &args);

  bitwuzla::Term declare(expr::Expr fdecl);
  bitwuzla::Term mkApp(bitwuzla::Term f,
                       const std::vector<bitwuzla::Term> &args);
  bitwuzla::Term mkEq(bitwuzla::Term a, bitwuzla::Term b);
  bitwuzla::Term mkIte(bitwuzla::Term c, bitwuzla::Term t, bitwuzla::Term e);
  bitwuzla::Term mkStore(bitwuzla::Term a, bitwuzla::Term i, bitwuzla::Term v);

  bitwuzla::TermManager &m_tm;
  /// closed terms
  std::unordered_map<expr::Expr, bitwuzla::Term> m_cache;
  /// binders being encoded, innermost last
  std::vector<Scope> m_scopes;
  std::vector<std::pair<expr::Expr, bitwuzla::Term>> m_decls;
};
} // namespace solver
} // namespace seahorn
#endif
