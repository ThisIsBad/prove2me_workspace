import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem proposition_11 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (s : ScaleSeq d) (a b : ℝ) (hs : IsRegular μ s a b)
    (c : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : IsCoeffRow c n)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0) (hf : Measurable f) (hfi : ∫⁻ x, (f x : ℝ≥0∞) ∂μ < ∞) :
    ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (StoneRegression.Criterion.wAt (nnWeights c s) n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤
      (beta d (a / b) : ℝ≥0∞) * ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by sorry

end StoneRegression.NearestNeighbor

