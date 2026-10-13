import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Remark 7.12, p. 982: under the conditions of Theorem 7.6,
`lim_{t → ∞} m_t(ξ) = 0` for every finite `ξ`. -/
theorem remark_7_12 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k / μ < k / (2 * (d : ℝ) - 1)) :
    ∀ ξ : HarrisContact.Extinction.Config d, Tendsto (fun t : ℝ => HarrisContact.Extinction.meanSize μ lam t ξ) atTop (𝓝 0) := by sorry
end HarrisContact.MeanSize

