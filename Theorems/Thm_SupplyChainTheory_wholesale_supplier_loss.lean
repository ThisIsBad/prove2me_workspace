import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem wholesale_supplier_loss (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D)
    (hps : 0 < P.ps) (hQ0 : (P.c - P.v) / (P.r - P.v + P.p) < 1 - ProbabilityTheory.cdf D 0)
    (Q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) :
    supplierProfit P D (wholesaleTransfer (wholesaleCoordPrice P)) Q0 < 0 := by sorry

end SupplyChainTheory
