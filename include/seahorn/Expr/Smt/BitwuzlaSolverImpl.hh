#ifdef WITH_BITWUZLA
#pragma once

#include "bitwuzla/cpp/bitwuzla.h"
#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"
#include "seahorn/Expr/Smt/Solver.hh"

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

namespace llvm {
class raw_ostream;
}

namespace seahorn {
namespace solver {

/// \brief The Solver interface on top of Bitwuzla
///
/// Unlike z3_solver_impl, every change (add, push, pop, reset, and a new
/// check) invalidates the last result, its model and its core.
///
/// An assertion that cannot be encoded makes add() return false. Since
/// callers may ignore that, the solver also remembers it: every check
/// answers UNKNOWN until a pop() or reset() removes the assertion.
///
/// Bitwuzla reports errors with exceptions. Every method catches them, so
/// none escapes into SeaHorn, which may be compiled without exceptions.
class bitwuzla_solver_impl : public Solver {
public:
  using model_ref = typename Solver::model_ref;

  explicit bitwuzla_solver_impl(expr::ExprFactory &efac,
                                bool produce_unsat_cores = false);
  ~bitwuzla_solver_impl() override;

  SolverKind get_kind() const override { return SolverKind::BITWUZLA; }

  bool add(expr::Expr exp) override;

  /** Check for satisfiability */
  SolverResult check() override;

  /** Check with assumptions */
  SolverResult check_with_assumptions(const expr_const_it_range &lits) override;

  /** Return an unsatisfiable core: the original assumption Exprs */
  void unsat_core(expr::ExprVector &out) override;

  /** Push a context */
  void push() override;

  /** Pop a context */
  void pop() override;

  /** Get a model. Empty unless the last check was SAT. */
  model_ref get_model() override;

  /** Clear all assertions */
  void reset() override;

  /** Print asserted formulas to SMT-LIB format **/
  void to_smt_lib(llvm::raw_ostream &o) override;

  /// \brief Changes whenever the solver changes, so that a model can tell
  /// that it is stale
  uint64_t generation() const { return m_generation; }

  bitwuzla::Bitwuzla &get_bitwuzla() { return *m_bzla; }
  marshal_bitwuzla &get_marshal() { return m_marshal; }
  expr::ExprFactory &get_efac() { return m_efac; }

private:
  /// invalidates the last result, its model and its core
  void changed();
  SolverResult record(bitwuzla::Result r);
  void unsupported(const std::string &reason);

  expr::ExprFactory &m_efac;
  bitwuzla::Options m_options;
  // -- declared before everything that holds terms, so destroyed last
  bitwuzla::TermManager m_tm;
  marshal_bitwuzla m_marshal;
  std::unique_ptr<bitwuzla::Bitwuzla> m_bzla;

  SolverResult m_last_result = SolverResult::UNKNOWN;
  uint64_t m_generation = 0;
  unsigned m_depth = 0;

  /// the last check was check_with_assumptions()
  bool m_with_assumptions = false;
  /// its assumptions, encoded, and the original Exprs of each
  std::vector<bitwuzla::Term> m_assumption_terms;
  std::unordered_map<bitwuzla::Term, expr::ExprVector> m_assumptions;

  /// an assertion could not be encoded at this push depth (or below)
  bool m_incomplete = false;
  unsigned m_incomplete_depth = 0;
  std::string m_incomplete_reason;
};
} // namespace solver
} // namespace seahorn
#endif
