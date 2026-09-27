import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem wholesale_underorder (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D) (w : ℝ) (hw : P.cs < w)
    (Qr Q0 : ℝ) (hr : IsMaxOn (retailerProfit P D (wholesaleTransfer w)) Set.univ Qr)
    (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) : Qr < Q0 := by sorry

end SupplyChainTheory
