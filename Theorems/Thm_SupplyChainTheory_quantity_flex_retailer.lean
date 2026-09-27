import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem quantity_flex_retailer (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D) (delta : ℝ) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1) (Q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) :
    IsMaxOn (retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D Q0 delta) delta)) Set.univ Q0 := by sorry

end SupplyChainTheory
