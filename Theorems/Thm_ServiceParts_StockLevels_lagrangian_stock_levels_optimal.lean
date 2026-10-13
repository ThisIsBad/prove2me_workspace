import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem lagrangian_stock_levels_optimal {ι : Type*} [Fintype ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ : ℝ) (hθ : 0 < θ) :
    (∀ i, (stockSet (d i) (c i) θ).Nonempty) ∧
    ∀ sStar : ι → ℕ, (∀ i, IsLeast (stockSet (d i) (c i) θ) (sStar i)) →
      ∀ s : ι → ℕ, totalInvestment d c s ≤ totalInvestment d c sStar →
        totalBackorders d sStar ≤ totalBackorders d s := by sorry

end ServiceParts.StockLevels

