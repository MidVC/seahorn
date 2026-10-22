#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaModelImpl.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/Support/raw_ostream.h"

using namespace expr;
using bitwuzla::Term;

namespace seahorn {
namespace solver {

bitwuzla_model_impl::bitwuzla_model_impl(bitwuzla_solver_impl &solver)
    : m_solver(solver), m_generation(solver.generation()) {}

bool bitwuzla_model_impl::valid() const {
  if (m_solver.generation() == m_generation)
    return true;
  ERR << "Bitwuzla model used after the solver changed";
  return false;
}

Expr bitwuzla_model_impl::eval(Expr e, bool complete) {
  if (!valid())
    return Expr();
  if (isOpX<TRUE>(e) || isOpX<FALSE>(e) || bv::is_bvnum(e))
    return e;

  ExprFactory &efac = m_solver.get_efac();
  try {
    Term v = m_solver.get_bitwuzla().get_value(
        m_solver.get_marshal().encode_term(e));
    if (v.sort().is_bool())
      return v.is_true() ? mk<TRUE>(efac) : mk<FALSE>(efac);
    if (v.sort().is_bv())
      return bv::bvnum(expr::mpz_class(v.value<std::string>(10)),
                       v.sort().bv_size(), efac);
    LOG("bitwuzla", WARN << "Bitwuzla model: values of sort " << v.sort().str()
                         << " are not decoded yet";);
  } catch (UnsupportedExpr &ex) {
    LOG("bitwuzla", WARN << "Bitwuzla model cannot evaluate: " << ex.what(););
  } catch (std::exception &ex) {
    ERR << "Bitwuzla model eval failed: " << ex.what();
  }
  return e;
}

void bitwuzla_model_impl::print(llvm::raw_ostream &o) const {
  if (!valid())
    return;
  for (const auto &decl : m_solver.get_marshal().decls()) {
    try {
      Term v = m_solver.get_bitwuzla().get_value(decl.second);
      o << decl.second.str() << " = " << v.str() << "\n";
    } catch (std::exception &ex) {
      o << decl.second.str() << " = ? (" << ex.what() << ")\n";
    }
  }
}

} // namespace solver
} // namespace seahorn

#endif
