import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_GameTree

namespace TheoryOfGames.PerfectInfo

namespace GameTree

/-- The value given by the formula (15:12): the operations `M^{k}_{σ}` of (15:8) applied from the
last move back to the first — the expectation `∑ σ, p σ * f σ` at a chance move (`k = 0`),
`Max_σ f σ` at a personal move of player 1 (`k = 1`), `Min_σ f σ` at a personal move of
player 2 (`k = 2`) — and the payoff `𝔉₁(π)` of the play at a leaf. -/
noncomputable def backwardValue : GameTree → ℝ
  | leaf w => w
  | chance _ p next _ _ => ∑ σ, p σ * backwardValue (next σ)
  | move1 α hα next =>
      Finset.univ.sup' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ fun σ : Fin α => backwardValue (next σ)
  | move2 α hα next =>
      Finset.univ.inf' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ fun σ : Fin α => backwardValue (next σ)

end GameTree

end TheoryOfGames.PerfectInfo
