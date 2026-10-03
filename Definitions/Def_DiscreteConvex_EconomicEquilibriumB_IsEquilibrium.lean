import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SupplySet

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `((xh), (yl), p)` is an equilibrium for total initial endowment `x°`. -/
def IsEquilibrium {H L : Type*} [Fintype H] [Fintype L] (U : H → (K → ℤ) → WithBot ℝ)
    (C : L → (K → ℤ) → WithTop ℝ) (x0 : K → ℤ) (x : H → (K → ℤ)) (y : L → (K → ℤ)) (p : K → ℝ) :
    Prop :=
  (∀ h : H, x h ∈ DemandSet (U h) p) ∧ (∀ l : L, y l ∈ SupplySet (C l) p) ∧
  (∑ h, x h) = x0 + ∑ l, y l ∧ (∀ k : K, 0 ≤ p k)

end DiscreteConvex.EconomicEquilibriumB
