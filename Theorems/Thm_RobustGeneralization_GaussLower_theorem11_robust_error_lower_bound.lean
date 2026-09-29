import Mathlib
import Definitions.Def_RobustGeneralization_GaussLower_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussLower

theorem theorem11_robust_error_lower_bound (d n : ℕ)
    (g : (Fin n → E d × Bool) → E d → Bool)
    (hg : Measurable (fun q : (Fin n → E d × Bool) × E d => g q.1 q.2))
    (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    (1 / 2 : ℝ≥0∞) *
        stdGaussian (E d) {v | ∀ i, Real.sqrt (n / (σ ^ 2 + n)) * |v i| ≤ ε} ≤
      expRobErr g σ ε := by sorry

end RobustGeneralization.GaussLower
