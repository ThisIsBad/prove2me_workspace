import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem buyback_coordinates (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ P.r - P.v + P.pr) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q →
        IsMaxOn (retailerProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
        ∧ IsMaxOn (supplierProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q)
      ∧ (b < P.r - P.v + P.pr → ∀ Q,
          IsMaxOn (retailerProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
            → IsMaxOn (chainProfit P D) Set.univ Q)
      ∧ (0 < b + P.ps → ∀ Q,
          IsMaxOn (supplierProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
            → IsMaxOn (chainProfit P D) Set.univ Q) := by sorry

end SupplyChainTheory
