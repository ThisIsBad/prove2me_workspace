import Mathlib

namespace TheoryOfGames.PerfectInfo

/-- A finite zero-sum two-person game with perfect information, as a finite game tree.
A `leaf w` is a play that has ended, with payoff `w = 𝔉₁(π)` to player 1 (player 2 receives `-w`).
An internal node is a move `𝔐` with alternatives `σ : Fin α`:
* `chance α p next hp hsum` — a chance move whose alternative `σ` has probability `p σ`
  (`p σ ≥ 0`, `∑ σ, p σ = 1`), after which the game continues as `next σ`;
* `move1 α hα next` — a personal move of player 1 with `α ≥ 1` alternatives;
* `move2 α hα next` — a personal move of player 2 with `α ≥ 1` alternatives. -/
inductive GameTree : Type
  | leaf (w : ℝ) : GameTree
  | chance (α : ℕ) (p : Fin α → ℝ) (next : Fin α → GameTree)
      (hp : ∀ σ, 0 ≤ p σ) (hsum : ∑ σ, p σ = 1) : GameTree
  | move1 (α : ℕ) (hα : 0 < α) (next : Fin α → GameTree) : GameTree
  | move2 (α : ℕ) (hα : 0 < α) (next : Fin α → GameTree) : GameTree

namespace GameTree

/-- The games `Γ_{σ₁}` that remain after the first move `𝔐₁` of `Γ` (empty for a game of
length zero). -/
def firstMoveSubgames : GameTree → Set GameTree
  | leaf _ => ∅
  | chance _ _ next _ _ => Set.range next
  | move1 _ _ next => Set.range next
  | move2 _ _ next => Set.range next

end GameTree

end TheoryOfGames.PerfectInfo
