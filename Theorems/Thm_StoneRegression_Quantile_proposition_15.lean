import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 15, p. 617, for one `n ≥ 1`: if `Wₙ` is a (Borel) probability weight function satisfying
(1) at this `n` with constant `C ≥ 1`, then for `0 < p < 1`, `M > 0` and `r ≥ 1`,
`E|L̂ₙ(p|X)|ʳ I{|L̂ₙ(p|X)| ≥ M} ≤ C/(p ∧ (1 − p)) · E|Y|ʳ I{|Y| ≥ M}`, and the same with `Ûₙ(p|X)`.
The page leaves `r` unquantified; `r ≥ 1` is the range Theorem 3 uses. -/
theorem proposition_15 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ) (hn : 1 ≤ n)
    (hWn : Measurable
      (fun q : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => W n q.1 q.2))
    (hPn : ∀ x xs, (∀ i, 0 ≤ W n x xs i) ∧ ∑ i, W n x xs i = 1)
    (C : ℝ≥0) (hC : 1 ≤ C)
    (h1 : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f →
      ∫⁻ ω, ∑ i : Fin n, ‖StoneRegression.Criterion.wAt W n ω i‖ₑ * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤ C * ∫⁻ x, f x ∂μ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (M : ℝ) (hM : 0 < M) (r : ℝ) (hr : 1 ≤ r)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    ∫⁻ ω, ‖estLowerQ W n p ω‖ₑ ^ r * (if M ≤ |estLowerQ W n p ω| then 1 else 0) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
        ((C : ℝ≥0∞) / ENNReal.ofReal (min p (1 - p))) *
          ∫⁻ q, ‖q.2‖ₑ ^ r * (if M ≤ |q.2| then 1 else 0) ∂(μ ⊗ₘ κ) ∧
    ∫⁻ ω, ‖estUpperQ W n p ω‖ₑ ^ r * (if M ≤ |estUpperQ W n p ω| then 1 else 0) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
        ((C : ℝ≥0∞) / ENNReal.ofReal (min p (1 - p))) *
          ∫⁻ q, ‖q.2‖ₑ ^ r * (if M ≤ |q.2| then 1 else 0) ∂(μ ⊗ₘ κ) := by sorry

end StoneRegression.Quantile

