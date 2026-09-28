import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem eq5_posterior_odds_likelihood_ratio (n : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1 / 2)
    (S : Fin n → Bool × Bool) :
    odds1 τ S = ∏ k, ((1 / 2 + τ) / (1 / 2 - τ)) ^ (lab (S k).2 * lab (S k).1) := by sorry

end RobustGeneralization.BernLower
