import Mathlib
import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem optimal_allocation (V : PrivateValues) (hV : V.IsRegular)
    (hJ : MonotoneOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) (v : Fin V.N → ℝ)
    (hv : ∀ i, v i ∈ Set.Icc 0 V.vbar) (y : Fin V.N → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hC : ∑ i, y i ≤ C) :
    ∑ i, virtualValue V (v i) * y i ≤
      ∑ i, virtualValue V (v i) * (secondPriceReserve V.N C vstar).y v i := by sorry

end RevenueManagement
