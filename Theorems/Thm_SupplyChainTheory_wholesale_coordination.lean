import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem wholesale_coordination (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D)
    (hps : 0 < P.ps) (hQ0 : (P.c - P.v) / (P.r - P.v + P.p) < 1 - ProbabilityTheory.cdf D 0) (w : ℝ) :
    ((∀ Q, IsMaxOn (retailerProfit P D (wholesaleTransfer w)) Set.univ Q
          ↔ IsMaxOn (chainProfit P D) Set.univ Q)
        ∧ (∀ Q, IsMaxOn (supplierProfit P D (wholesaleTransfer w)) Set.univ Q
          ↔ IsMaxOn (chainProfit P D) Set.univ Q))
      ↔ w = wholesaleCoordPrice P := by sorry

end SupplyChainTheory
