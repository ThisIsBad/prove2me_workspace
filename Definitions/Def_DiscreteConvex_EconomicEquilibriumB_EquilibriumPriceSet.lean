import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SupplySet

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The set of all equilibrium price vectors for the given allocation `(x,y)`, Eq. (11.23). -/
def EquilibriumPriceSet {H L : Type*} [Fintype H] [Fintype L] (U : H → (K → ℤ) → WithBot ℝ)
    (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ)) (y : L → (K → ℤ)) : Set (K → ℝ) :=
  {p | (∀ h : H, x h ∈ DemandSet (U h) p) ∧ (∀ l : L, y l ∈ SupplySet (C l) p) ∧ ∀ k, 0 ≤ p k}

end DiscreteConvex.EconomicEquilibriumB
