import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ContDemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ContSupplySet

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `((xh), (yl), p)` is an equilibrium of the derived continuous economy for `x°`. -/
def IsContEquilibrium {H L : Type*} [Fintype H] [Fintype L] (U : H → (K → ℤ) → WithBot ℝ)
    (C : L → (K → ℤ) → WithTop ℝ) (x0 : K → ℤ) (x : H → (K → ℝ)) (y : L → (K → ℝ)) (p : K → ℝ) :
    Prop :=
  (∀ h : H, x h ∈ ContDemandSet (U h) p) ∧ (∀ l : L, y l ∈ ContSupplySet (C l) p) ∧
  (∑ h, x h) = (fun k => (x0 k : ℝ)) + ∑ l, y l ∧ (∀ k : K, 0 ≤ p k)

-- ===== The gross-substitutes-style characterizations (§11.3) =====

end DiscreteConvex.EconomicEquilibriumB
