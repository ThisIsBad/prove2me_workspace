import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Theorem 7.6, p. 982: if `λ_k/μ < k/(2d − 1)` for `k = 1, …, 2d`, then
`∫_0^∞ m_t(ξ) dt < ∞` for every finite `ξ`. -/
theorem theorem_7_6 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k / μ < k / (2 * (d : ℝ) - 1)) :
    ∀ ξ : HarrisContact.Extinction.Config d, ∫⁻ t in Set.Ioi (0 : ℝ), HarrisContact.Extinction.meanSize μ lam t ξ < ∞ := by sorry
end HarrisContact.MeanSize

