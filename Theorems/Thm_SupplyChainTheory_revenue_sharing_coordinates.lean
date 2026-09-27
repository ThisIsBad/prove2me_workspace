import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem revenue_sharing_coordinates (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (phi : ℝ) (h0 : 0 ≤ phi) (h1 : phi ≤ 1) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q →
        IsMaxOn (retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
          Set.univ Q
        ∧ IsMaxOn (supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
          Set.univ Q)
      ∧ (0 < phi * (P.r - P.v) + P.pr → ∀ Q,
          IsMaxOn (retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
            Set.univ Q → IsMaxOn (chainProfit P D) Set.univ Q)
      ∧ (phi * (P.r - P.v) + P.pr < P.r - P.v + P.p → ∀ Q,
          IsMaxOn (supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
            Set.univ Q → IsMaxOn (chainProfit P D) Set.univ Q) := by sorry

end SupplyChainTheory
