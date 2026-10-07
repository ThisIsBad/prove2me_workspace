import Definitions.Def_HartSchmeidler_FinStrat_Game

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Proof of Theorem 2, pp. 22–23: every f-set game Γ_T has a finite-support
correlated equilibrium, whether or not the payoff functions are continuous. -/
theorem fset_game_has_ce {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    (h : ι → (∀ i, S i) → ℝ)
    (hbounded : ∀ i, ∃ C : ℝ, ∀ s, |h i s| ≤ C)
    (T : ∀ i, Finset (S i))
    (hT : IsFSet T) :
    ∃ (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ), IsFSetCE h T F w := by sorry

end HartSchmeidler.FinStrat

