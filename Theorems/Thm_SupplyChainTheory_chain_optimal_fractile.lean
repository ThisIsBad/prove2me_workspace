import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem chain_optimal_fractile (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q ↔ 1 - ProbabilityTheory.cdf D Q = (P.c - P.v) / (P.r - P.v + P.p))
      ∧ ∃ Q0, IsMaxOn (chainProfit P D) Set.univ Q0 := by sorry

end SupplyChainTheory
