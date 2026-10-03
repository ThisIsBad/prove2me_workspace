import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MExchangeAxiomW
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QM
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQM
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeight

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.68 (p.171). GOAL. The quasi M-convexity hierarchy: the implication diagram
relating (M-EXC[Z]), (SSQM), (QM) and their weak variants, and the identification of
(M-EXC[Z]) with (QMw) holding for every linear perturbation of `f`. -/
theorem quasi_mconvex_hierarchy (f : (V → ℤ) → WithTop ℝ) :
    (MExchangeAxiom f → SSQM f) ∧
    (SSQM f → QM f) ∧
    (MExchangeAxiomW f → SSQMw f) ∧
    (SSQMw f → QMw f) ∧
    (MExchangeAxiom f ↔ MExchangeAxiomW f) ∧
    (SSQM f → SSQMw f) ∧
    (QM f → QMw f) ∧
    (MExchangeAxiom f ↔ ∀ p : V → ℝ, QMw (LinearWeight f p)) := by sorry

end DiscreteConvex.MConvexFunctionsE
