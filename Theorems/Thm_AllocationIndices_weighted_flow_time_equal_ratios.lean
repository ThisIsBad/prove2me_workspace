import Definitions.Def_AllocationIndices_Jobs

open MeasureTheory ProbabilityTheory BanditAlgorithm


namespace AllocationIndices

theorem weighted_flow_time_equal_ratios {n m : ℕ} (σ : Schedule n m) (s c : Fin n → ℝ)
    (hm : 0 < m) {κ : ℝ} (hc : ∀ i, c i = κ * s i) :
    weightedFlowTime σ s c =
      κ / 2 * (∑ i, s i ^ 2 + (∑ i, s i) ^ 2 / m + ∑ j, loadDeviation σ s j ^ 2) := by sorry

end AllocationIndices

