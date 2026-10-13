import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- Theorem 7.1 (p. 981): if (2d − 1)λ_k < kμ for k = 1, …, 2d, then p_∞(ξ) = 0 for every
finite ξ. -/
theorem theorem_7_1 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → (2 * (d : ℝ) - 1) * lam k < k * μ) :
    ∀ ξ : Config d, survInf μ lam ξ = 0 := by sorry

end HarrisContact.Extinction

