import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_GameTree

namespace TheoryOfGames.PerfectInfo

namespace GameTree

/-- A pure strategy of player 1: a complete plan choosing an alternative at every personal
move of player 1 in the tree, reached or not. -/
def Strategy1 : GameTree → Type
  | leaf _ => Unit
  | chance α _ next _ _ => (σ : Fin α) → Strategy1 (next σ)
  | move1 α _ next => Fin α × ((σ : Fin α) → Strategy1 (next σ))
  | move2 α _ next => (σ : Fin α) → Strategy1 (next σ)

/-- A pure strategy of player 2: a complete plan choosing an alternative at every personal
move of player 2 in the tree, reached or not. -/
def Strategy2 : GameTree → Type
  | leaf _ => Unit
  | chance α _ next _ _ => (σ : Fin α) → Strategy2 (next σ)
  | move1 α _ next => (σ : Fin α) → Strategy2 (next σ)
  | move2 α _ next => Fin α × ((σ : Fin α) → Strategy2 (next σ))

/-- Each player has finitely many pure strategies. -/
instance instFintypeStrategy1 : (t : GameTree) → Fintype (Strategy1 t)
  | leaf _ => inferInstanceAs (Fintype Unit)
  | chance α _ next _ _ =>
      letI := fun σ => instFintypeStrategy1 (next σ)
      inferInstanceAs (Fintype ((σ : Fin α) → Strategy1 (next σ)))
  | move1 α _ next =>
      letI := fun σ => instFintypeStrategy1 (next σ)
      inferInstanceAs (Fintype (Fin α × ((σ : Fin α) → Strategy1 (next σ))))
  | move2 α _ next =>
      letI := fun σ => instFintypeStrategy1 (next σ)
      inferInstanceAs (Fintype ((σ : Fin α) → Strategy1 (next σ)))

instance instFintypeStrategy2 : (t : GameTree) → Fintype (Strategy2 t)
  | leaf _ => inferInstanceAs (Fintype Unit)
  | chance α _ next _ _ =>
      letI := fun σ => instFintypeStrategy2 (next σ)
      inferInstanceAs (Fintype ((σ : Fin α) → Strategy2 (next σ)))
  | move1 α _ next =>
      letI := fun σ => instFintypeStrategy2 (next σ)
      inferInstanceAs (Fintype ((σ : Fin α) → Strategy2 (next σ)))
  | move2 α _ next =>
      letI := fun σ => instFintypeStrategy2 (next σ)
      inferInstanceAs (Fintype (Fin α × ((σ : Fin α) → Strategy2 (next σ))))

/-- Each player has at least one pure strategy (every personal move has `α ≥ 1`). -/
instance instNonemptyStrategy1 : (t : GameTree) → Nonempty (Strategy1 t)
  | leaf _ => inferInstanceAs (Nonempty Unit)
  | chance α _ next _ _ =>
      letI := fun σ => instNonemptyStrategy1 (next σ)
      inferInstanceAs (Nonempty ((σ : Fin α) → Strategy1 (next σ)))
  | move1 α hα next =>
      letI := fun σ => instNonemptyStrategy1 (next σ)
      letI : Nonempty (Fin α) := ⟨⟨0, hα⟩⟩
      inferInstanceAs (Nonempty (Fin α × ((σ : Fin α) → Strategy1 (next σ))))
  | move2 α _ next =>
      letI := fun σ => instNonemptyStrategy1 (next σ)
      inferInstanceAs (Nonempty ((σ : Fin α) → Strategy1 (next σ)))

instance instNonemptyStrategy2 : (t : GameTree) → Nonempty (Strategy2 t)
  | leaf _ => inferInstanceAs (Nonempty Unit)
  | chance α _ next _ _ =>
      letI := fun σ => instNonemptyStrategy2 (next σ)
      inferInstanceAs (Nonempty ((σ : Fin α) → Strategy2 (next σ)))
  | move1 α _ next =>
      letI := fun σ => instNonemptyStrategy2 (next σ)
      inferInstanceAs (Nonempty ((σ : Fin α) → Strategy2 (next σ)))
  | move2 α hα next =>
      letI := fun σ => instNonemptyStrategy2 (next σ)
      letI : Nonempty (Fin α) := ⟨⟨0, hα⟩⟩
      inferInstanceAs (Nonempty (Fin α × ((σ : Fin α) → Strategy2 (next σ))))

/-- The normalized form `ℋ(τ₁, τ₂)`: the mathematical expectation, over the chance moves, of
the payoff to player 1 of the play produced when player 1 uses `τ₁` and player 2 uses `τ₂`. -/
def payoff : (t : GameTree) → Strategy1 t → Strategy2 t → ℝ
  | leaf w, _, _ => w
  | chance _ p next _ _, τ₁, τ₂ => ∑ σ, p σ * payoff (next σ) (τ₁ σ) (τ₂ σ)
  | move1 _ _ next, τ₁, τ₂ => payoff (next τ₁.1) (τ₁.2 τ₁.1) (τ₂ τ₁.1)
  | move2 _ _ next, τ₁, τ₂ => payoff (next τ₂.1) (τ₁ τ₂.1) (τ₂.2 τ₂.1)

end GameTree

end TheoryOfGames.PerfectInfo
