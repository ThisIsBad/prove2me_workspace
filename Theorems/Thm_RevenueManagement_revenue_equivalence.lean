import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem revenue_equivalence (V : PrivateValues) (hV : V.IsRegular) (C : ℕ) (M : Mechanism V.N)
    (hM : M.IsFeasible C V.vbar) (hmono : HasMonotoneAllocation V M) (hzero : HasZeroSurplusAtZero V M)
    (hic : IsIncentiveCompatible V M) :
    expRevenue V M = ∫ v, ∑ i, virtualValue V (v i) * M.y v i ∂V.joint ∧
    ∀ i, ∀ w ∈ Set.Icc 0 V.vbar,
      expPayment V M i w = w * winProb V M i w - ∫ s in (0 : ℝ)..w, winProb V M i s := by sorry

end RevenueManagement
