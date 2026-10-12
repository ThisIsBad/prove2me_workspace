import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), §2, p. 536, (2.3)–(2.5). For `λ > 0` and bounded `h`, the function `S_λh` of
(2.5) (first line) solves the Stein equation `wf(w) − λf(w + 1) = h(w) − 𝒫_λh` for every `w ≥ 0`,
and for `w ≥ 1` it also has the tail form
`S_λh(w) = (w − 1)! λ^{−w} Σ_{k=w}^∞ [h(k) − 𝒫_λh] λ^k / k!` (second line of (2.5)). -/
theorem stein_solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ)
    (hM : ∀ k, |h k| ≤ M) :
    (∀ w : ℕ, (w : ℝ) * stein lam h w - lam * stein lam h (w + 1) = h w - poissonExp lam h) ∧
    (∀ w : ℕ, 1 ≤ w → stein lam h w = ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
      ∑' k : ℕ, (h (k + w) - poissonExp lam h) * lam ^ (k + w) / ((k + w).factorial : ℝ)) := by sorry

end PoissonDepTrials.MixSqrt

