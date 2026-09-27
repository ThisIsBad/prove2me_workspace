import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem buyback_profit_identities (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (b Q : ℝ) :
    retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = buybackShare P b * chainProfit P D Q
          + meanDemand D * (buybackShare P b * P.p - P.pr)
      ∧ supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = (1 - buybackShare P b) * chainProfit P D Q
          - meanDemand D * (buybackShare P b * P.p - P.pr) := by sorry

end SupplyChainTheory
