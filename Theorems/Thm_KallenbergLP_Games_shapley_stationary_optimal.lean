import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.1 (Shapley 1953; p. 192): under Assumption 6.2.1 there exist stationary optimal
policies for both players. -/
theorem shapley_stationary_optimal {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) :
    ∃ (π : Fin N → α → ℝ) (ρ : Fin N → β → ℝ) (hπ : IsDecisionRule1 G π)
      (hρ : IsDecisionRule2 G ρ), IsOptimalPair G (stationary1 G π hπ) (stationary2 G ρ hρ) := by sorry

end KallenbergLP.Games

