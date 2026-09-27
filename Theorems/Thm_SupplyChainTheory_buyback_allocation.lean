import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem buyback_allocation (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (hmu : 0 < meanDemand D)
    (hps : 0 < P.ps) (hpr : 0 < P.pr)
    (Q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) (hpos : 0 < chainProfit P D Q0) :
    let πr := fun b => retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    let πs := fun b => supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q0
    let b1 := buybackB1 P D Q0
    let b2 := buybackB2 P D Q0
    StrictAntiOn πr (Set.Icc 0 (P.r - P.v + P.pr))
      ∧ StrictMonoOn πs (Set.Icc 0 (P.r - P.v + P.pr))
      ∧ 0 < b1 ∧ b1 < b2 ∧ b2 < P.r - P.v + P.pr
      ∧ (∀ b, 0 ≤ b → b < b1 → πs b < 0 ∧ chainProfit P D Q0 < πr b)
      ∧ πr b1 = chainProfit P D Q0
      ∧ (∀ b, b1 < b → b < b2 → 0 < πr b ∧ 0 < πs b)
      ∧ πs b2 = chainProfit P D Q0
      ∧ (∀ b, b2 < b → b ≤ P.r - P.v + P.pr → πr b < 0 ∧ chainProfit P D Q0 < πs b) := by sorry

end SupplyChainTheory
