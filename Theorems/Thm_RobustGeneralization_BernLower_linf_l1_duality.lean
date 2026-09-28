import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem linf_l1_duality (d : ℕ) (w x : E d) (y : Bool) (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest {t : ℝ | ∃ Δ : E d, (∀ i, |Δ i| ≤ ε) ∧ t = inner ℝ (lab y • w) Δ}
        (ε * ∑ i, |w i|) ∧
      ((∀ x' ∈ linfBall x ε, 0 < inner ℝ (lab y • w) x') ↔
        ε * ∑ i, |w i| < inner ℝ (lab y • w) x) := by sorry

end RobustGeneralization.BernLower
