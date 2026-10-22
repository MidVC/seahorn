#ifdef WITH_BITWUZLA
#pragma once

#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/Smt/Model.hh"

namespace seahorn {
namespace solver {

/// \brief A view of the model of the last SAT check of a
/// bitwuzla_solver_impl
///
/// The model is valid only until the solver changes. After that, eval()
/// reports an error and returns a null Expr instead of a value from another
/// state. The solver must outlive the model.
///
/// Values of Bool and bit-vector terms are decoded; other terms are
/// returned unchanged (arrays and functions come with plan step 1.5).
class bitwuzla_model_impl : public Model {
  bitwuzla_solver_impl &m_solver;
  uint64_t m_generation;

  bool valid() const;

public:
  explicit bitwuzla_model_impl(bitwuzla_solver_impl &solver);

  /// Bitwuzla assigns a value to every term, so \p complete has no effect:
  /// both settings return completed values
  expr::Expr eval(expr::Expr e, bool complete) override;

  /// Prints the value of every constant the solver has declared
  void print(llvm::raw_ostream &o) const override;
};
} // namespace solver
} // namespace seahorn
#endif
