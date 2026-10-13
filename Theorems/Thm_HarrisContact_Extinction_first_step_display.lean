import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- §7, display before Theorem 7.1 (p. 981): for a subadditive process and n ≥ 1,
p_∞(x) is harmonic for r^{(n)} and is at most p_∞(x) 𝓔_x |ξ_{(n)}|. -/
theorem first_step_display {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ)
    (h0 : lam 0 = 0) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsubadd : ∀ t : ℝ, 0 ≤ t → ∀ ξ η : Config d,
      surv μ lam t (ξ ∪ η) ≤ surv μ lam t ξ + surv μ lam t η) :
    ∀ (n : ℕ), 1 ≤ n → ∀ x : Site d,
      (survInf μ lam {x} =
          ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n {x} η) * survInf μ lam η) ∧
        survInf μ lam {x} ≤
          survInf μ lam {x} *
            ∑' η : Config d, ENNReal.ofReal (jumpPow μ lam n {x} η) * (η.card : ℝ≥0∞) := by sorry

end HarrisContact.Extinction

