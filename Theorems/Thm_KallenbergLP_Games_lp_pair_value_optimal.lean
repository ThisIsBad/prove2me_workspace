import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.3 (p. 195): under Assumptions 6.2.1 and 6.2.2, with `β ≫ 0`, let `(y*, ρ*)` and
`(x*, z*)` be optimal solutions of (6.2.1) and (6.2.2), and `π*_{ia} := x*_{ia} / ∑_a x*_{ia}`.
Then `(π*)^∞` and `(ρ*)^∞` are stationary optimal policies for player I and player II, and
`y* = v((π*)^∞, (ρ*)^∞)` is the value of the game. -/
theorem lp_pair_value_optimal {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (ys : Fin N → ℝ) (ρs : Fin N → β → ℝ) (h1 : LP621Optimal G β' ys ρs)
    (xs : Fin N → α → ℝ) (zs : Fin N → ℝ) (h2 : LP622Optimal G β' xs zs) :
    ∃ (hπ : IsDecisionRule1 G (piOfX G xs)) (hρ : IsDecisionRule2 G ρs),
      IsOptimalPair G (stationary1 G (piOfX G xs) hπ) (stationary2 G ρs hρ) ∧
        ∀ i, ys i = totalReward G (stationary1 G (piOfX G xs) hπ) (stationary2 G ρs hρ) i := by sorry

end KallenbergLP.Games

