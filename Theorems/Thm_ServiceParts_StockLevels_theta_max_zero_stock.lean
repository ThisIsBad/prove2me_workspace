import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem theta_max_zero_stock {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ i, 0 < thetaZero (d i) (c i) ∧
      (d i).pmf 0 = 1 / (1 + thetaZero (d i) (c i) * c i)) ∧
    ∀ i, IsLeast
      (stockSet (d i) (c i) (Finset.univ.sup' Finset.univ_nonempty
        (fun j => thetaZero (d j) (c j)))) 0 := by sorry

end ServiceParts.StockLevels

