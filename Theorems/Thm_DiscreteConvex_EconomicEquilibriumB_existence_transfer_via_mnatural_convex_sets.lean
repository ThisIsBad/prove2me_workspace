import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SupplySet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsEquilibrium
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsMNaturalConvexSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsContEquilibrium

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Theorem 11.15 (p.339). If demand and supply sets are M♮-convex whenever nonempty, and the
derived continuous economy has an equilibrium for `x° ∈ Zᴷ₊`, then an equilibrium of indivisible
commodities exists for `x°`. -/
theorem existence_transfer_via_mnatural_convex_sets {H L : Type*} [Fintype H] [Fintype L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ)
    (hD : ∀ p : K → ℝ, (∀ k, 0 ≤ p k) → ∀ h, (DemandSet (U h) p).Nonempty →
      IsMNaturalConvexSet (DemandSet (U h) p))
    (hS : ∀ p : K → ℝ, (∀ k, 0 ≤ p k) → ∀ l, (SupplySet (C l) p).Nonempty →
      IsMNaturalConvexSet (SupplySet (C l) p))
    (x0 : K → ℤ) (hx0 : ∀ k, 0 ≤ x0 k) (xc : H → (K → ℝ)) (yc : L → (K → ℝ)) (pc : K → ℝ)
    (hcont : IsContEquilibrium U C x0 xc yc pc) :
    ∃ (x : H → (K → ℤ)) (y : L → (K → ℤ)) (p : K → ℝ), IsEquilibrium U C x0 x y p := by sorry

end DiscreteConvex.EconomicEquilibriumB
