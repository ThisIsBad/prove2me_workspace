import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem list_price_unconstrained_optimal (V : PrivateValues) (hV : V.IsRegular)
    (hJ : StrictMonoOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (hNC : V.N ≤ C) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) (M : Mechanism V.N)
    (hM : M.IsFeasible C V.vbar) (hmono : HasMonotoneAllocation V M) (hzero : HasZeroSurplusAtZero V M)
    (hic : IsIncentiveCompatible V M) :
    expRevenue V M ≤ expRevenue V (listPrice V.N vstar) := by sorry

end RevenueManagement
