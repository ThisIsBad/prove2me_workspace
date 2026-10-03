import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightPlus

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.49 (p.199). The quasi-submodularity hierarchy: the implication diagram relating
(SBF[Z]), (SSQSB), (QSB) and their weak variants, and the identification of (SBF[Z]) with (QSBw)
holding for every linear perturbation of `g`. -/
theorem quasi_submodular_hierarchy (g : (V → ℤ) → WithTop ℝ) :
    (SBF g → SSQSB g) ∧ (SSQSB g → QSB g) ∧
    (SSQSB g → SSQSBw g) ∧ (QSB g → QSBw g) ∧
    (SBF g ↔ ∀ x : V → ℝ, QSBw (LinearWeightPlus g x)) := by sorry

end DiscreteConvex.LConvexFunctionsD
