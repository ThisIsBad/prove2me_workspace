import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem reserve_price_auction_optimal (V : PrivateValues) (hV : V.IsRegular)
    (hJ : StrictMonoOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) :
    ((secondPriceReserve V.N C vstar).IsFeasible C V.vbar ∧
      HasMonotoneAllocation V (secondPriceReserve V.N C vstar) ∧
      HasZeroSurplusAtZero V (secondPriceReserve V.N C vstar) ∧
      IsIncentiveCompatible V (secondPriceReserve V.N C vstar)) ∧
    ∀ M : Mechanism V.N, M.IsFeasible C V.vbar → HasMonotoneAllocation V M → HasZeroSurplusAtZero V M →
      IsIncentiveCompatible V M → expRevenue V M ≤ expRevenue V (secondPriceReserve V.N C vstar) := by sorry

end RevenueManagement
