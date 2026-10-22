#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/Smt/BitwuzlaModelImpl.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <cstring>
#include <sstream>

using namespace expr;
using bitwuzla::Option;
using bitwuzla::Term;

namespace seahorn {
namespace solver {

bitwuzla_solver_impl::bitwuzla_solver_impl(ExprFactory &efac,
                                           bool produce_unsat_cores)
    : Solver(), m_efac(efac), m_marshal(m_tm) {
  try {
    // -- options must be set before the Bitwuzla instance is created
    m_options.set(Option::PRODUCE_MODELS, true);
    m_options.set(Option::PRODUCE_UNSAT_ASSUMPTIONS, true);
    // -- cores of assertions (not of assumptions) cost time; plan 3.3
    if (produce_unsat_cores)
      m_options.set(Option::PRODUCE_UNSAT_CORES, true);
    m_bzla = std::make_unique<bitwuzla::Bitwuzla>(m_tm, m_options);
  } catch (std::exception &ex) {
    llvm::report_fatal_error(
        llvm::StringRef(std::string("cannot create Bitwuzla: ") + ex.what()));
  }
}

bitwuzla_solver_impl::~bitwuzla_solver_impl() = default;

void bitwuzla_solver_impl::changed() {
  ++m_generation;
  m_last_result = SolverResult::UNKNOWN;
  m_with_assumptions = false;
  m_assumption_terms.clear();
  m_assumptions.clear();
}

SolverResult bitwuzla_solver_impl::record(bitwuzla::Result r) {
  switch (r) {
  case bitwuzla::Result::SAT:
    m_last_result = SolverResult::SAT;
    break;
  case bitwuzla::Result::UNSAT:
    m_last_result = SolverResult::UNSAT;
    break;
  case bitwuzla::Result::UNKNOWN:
    m_last_result = SolverResult::UNKNOWN;
    break;
  }
  return m_last_result;
}

void bitwuzla_solver_impl::unsupported(const std::string &reason) {
  // -- keep the first reason
  if (m_incomplete)
    return;
  m_incomplete = true;
  m_incomplete_depth = m_depth;
  m_incomplete_reason = reason;
  WARN << "Bitwuzla cannot encode an assertion, so checks answer unknown: "
       << reason;
}

bool bitwuzla_solver_impl::add(Expr exp) {
  changed();
  try {
    m_bzla->assert_formula(m_marshal.encode_term(exp));
    return true;
  } catch (UnsupportedExpr &ex) {
    unsupported(ex.what());
  } catch (std::exception &ex) {
    // -- e.g., an assertion that is not Boolean
    unsupported(ex.what());
  }
  return false;
}

SolverResult bitwuzla_solver_impl::check() {
  changed();
  if (m_incomplete) {
    LOG("bitwuzla", WARN << "answering unknown: " << m_incomplete_reason;);
    return m_last_result;
  }
  try {
    return record(m_bzla->check_sat());
  } catch (std::exception &ex) {
    ERR << "Bitwuzla check failed: " << ex.what();
  }
  m_last_result = SolverResult::ERROR;
  return m_last_result;
}

SolverResult
bitwuzla_solver_impl::check_with_assumptions(const expr_const_it_range &lits) {
  changed();
  m_with_assumptions = true;
  try {
    for (Expr lit : lits) {
      Term t = m_marshal.encode_term(lit);
      // -- the core must give back the caller's own Exprs (MUC relies on it)
      ExprVector &orig = m_assumptions[t];
      if (std::find(orig.begin(), orig.end(), lit) == orig.end())
        orig.push_back(lit);
      m_assumption_terms.push_back(t);
    }
  } catch (UnsupportedExpr &ex) {
    WARN << "Bitwuzla cannot encode an assumption, so the check answers "
            "unknown: "
         << ex.what();
    return m_last_result;
  }
  if (m_incomplete) {
    LOG("bitwuzla", WARN << "answering unknown: " << m_incomplete_reason;);
    return m_last_result;
  }
  try {
    return record(m_bzla->check_sat(m_assumption_terms));
  } catch (std::exception &ex) {
    ERR << "Bitwuzla check failed: " << ex.what();
  }
  m_last_result = SolverResult::ERROR;
  return m_last_result;
}

void bitwuzla_solver_impl::unsat_core(ExprVector &out) {
  if (!m_with_assumptions || m_last_result != SolverResult::UNSAT) {
    ERR << "Bitwuzla unsat_core: the last check was not an unsat check "
           "with assumptions";
    return;
  }
  try {
    for (const Term &t : m_bzla->get_unsat_assumptions()) {
      auto it = m_assumptions.find(t);
      if (it == m_assumptions.end()) {
        ERR << "Bitwuzla unsat_core: a core literal is not an assumption";
        continue;
      }
      out.insert(out.end(), it->second.begin(), it->second.end());
    }
  } catch (std::exception &ex) {
    ERR << "Bitwuzla unsat_core failed: " << ex.what();
  }
}

void bitwuzla_solver_impl::push() {
  changed();
  try {
    m_bzla->push(1);
    ++m_depth;
  } catch (std::exception &ex) {
    ERR << "Bitwuzla push failed: " << ex.what();
  }
}

void bitwuzla_solver_impl::pop() {
  changed();
  if (m_depth == 0) {
    ERR << "Bitwuzla pop: there is no context to pop";
    return;
  }
  try {
    m_bzla->pop(1);
    --m_depth;
  } catch (std::exception &ex) {
    ERR << "Bitwuzla pop failed: " << ex.what();
  }
  // -- the assertion that could not be encoded is gone
  if (m_incomplete && m_depth < m_incomplete_depth) {
    m_incomplete = false;
    m_incomplete_reason.clear();
  }
}

void bitwuzla_solver_impl::reset() {
  changed();
  // -- a fresh instance; the TermManager and the encoder's cache stay valid
  m_bzla.reset();
  try {
    m_bzla = std::make_unique<bitwuzla::Bitwuzla>(m_tm, m_options);
  } catch (std::exception &ex) {
    llvm::report_fatal_error(
        llvm::StringRef(std::string("cannot create Bitwuzla: ") + ex.what()));
  }
  m_depth = 0;
  m_incomplete = false;
  m_incomplete_reason.clear();
}

bitwuzla_solver_impl::model_ref bitwuzla_solver_impl::get_model() {
  if (m_last_result != SolverResult::SAT) {
    ERR << "Bitwuzla get_model: the last check was not sat";
    return model_ref();
  }
  return std::make_shared<bitwuzla_model_impl>(*this);
}

void bitwuzla_solver_impl::to_smt_lib(llvm::raw_ostream &o) {
  std::ostringstream os;
  try {
    m_bzla->print_formula(os, "smt2");
  } catch (std::exception &ex) {
    ERR << "Bitwuzla to_smt_lib failed: " << ex.what();
    return;
  }
  std::string smt = os.str();

  // -- after a check with assumptions, check those. A constant that occurs
  // -- only in an assumption is not declared by print_formula.
  if (m_with_assumptions) {
    std::string cmd = "(check-sat-assuming (";
    for (size_t i = 0, sz = m_assumption_terms.size(); i < sz; ++i)
      cmd += (i ? " " : "") + m_assumption_terms[i].str();
    cmd += "))";
    const char *check_sat = "(check-sat)";
    size_t pos = smt.rfind(check_sat);
    if (pos != std::string::npos)
      smt.replace(pos, std::strlen(check_sat), cmd);
  }

  if (m_incomplete) {
    std::string reason = m_incomplete_reason;
    std::replace(reason.begin(), reason.end(), '\n', ' ');
    o << "; WARNING: an assertion could not be encoded and is missing: "
      << reason << "\n";
  }
  o << smt;
}

} // namespace solver
} // namespace seahorn

#endif
