#ifdef WITH_BITWUZLA
#pragma once

#include "bitwuzla/cpp/bitwuzla.h"
#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"
#include "seahorn/Expr/Smt/Solver.hh"

#include <memory>
#include <string>

namespace llvm {
class raw_ostream;
}

namespace seahorn {
namespace solver {

/// \brief The Solver interface on top of Bitwuzla
///
/// Only add(), check() and reset() are implemented so far. The other
/// methods print an error and exit, so that nothing mistakes them for a
/// real answer.
///
/// An assertion that cannot be encoded makes add() return false. Since
/// callers may ignore that (SolverBmc does), the solver also remembers it:
/// every check answers UNKNOWN until reset() removes it.
///
/// Bitwuzla reports errors with exceptions. Every method catches them, so
/// none escapes into SeaHorn, which may be compiled without them.
class bitwuzla_solver_impl : public Solver {
public:
  using model_ref = typename Solver::model_ref;

  bitwuzla_solver_impl();
  ~bitwuzla_solver_impl() override;

  SolverKind get_kind() const override { return SolverKind::BITWUZLA; }

  bool add(expr::Expr exp) override;

  /** Check for satisfiability */
  SolverResult check() override;

  /** Clear all assertions */
  void reset() override;

  /** Not supported yet */
  SolverResult check_with_assumptions(const expr_const_it_range &lits) override;
  void unsat_core(expr::ExprVector &out) override;
  void push() override;
  void pop() override;
  model_ref get_model() override;
  void to_smt_lib(llvm::raw_ostream &o) override;

private:
  bitwuzla::Options m_options;
  // -- declared before everything that holds terms, so destroyed last
  bitwuzla::TermManager m_tm;
  marshal_bitwuzla m_marshal;
  std::unique_ptr<bitwuzla::Bitwuzla> m_bzla;

  /// why an assertion could not be encoded; empty if every one was
  std::string m_unsupported;
};
} // namespace solver
} // namespace seahorn
#endif
