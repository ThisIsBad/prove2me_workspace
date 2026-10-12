import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory

namespace PoissonDepTrials.MixSqrt

/-- Chen (1975), Lemma 3.1, p. 536, (3.1): for `λ ≥ w` and `w ≥ 1`,
`(w − 1)! λ^{−w} Σ_{k=0}^{w−1} λ^k / k! ≤ 2λ^{−1/2}`. -/
theorem lemma_3_1 (lam : ℝ) (w : ℕ) (hw : 1 ≤ w) (hlw : (w : ℝ) ≤ lam) :
    ((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ * ∑ k ∈ Finset.range w, lam ^ k / (k.factorial : ℝ)
      ≤ 2 / Real.sqrt lam := by sorry

end PoissonDepTrials.MixSqrt

