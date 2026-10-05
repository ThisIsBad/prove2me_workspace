import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun

namespace TheoryOfGames.GeneralGames

namespace GeneralGame

variable {n : ℕ}

/-- Player `j` has *no influence upon the course of the game* `Γ` if all the functions
`ℋ_k(τ₁, …, τₙ)` are independent of the variable `τ_j` (the reading used in the proof of (57:C),
p. 534, and in 56.2.2 for the fictitious player). -/
def NoInfluence (Γ : GeneralGame n) (j : Fin n) : Prop :=
  ∀ τ τ' : (k : Fin n) → Fin (Γ.β k), (∀ i, i ≠ j → τ i = τ' i) → Γ.H τ = Γ.H τ'

/-- (57:A): for a zero-sum `n`-person game `Γ` and a set `S ⊆ I`, `S` is *removable* for `Γ`
if there is another zero-sum `n`-person game `Γ'` which has the same characteristic function as
`Γ` but in which no player belonging to `S` has an influence upon the course of the game.
(For zero-sum games the characteristic function of 25.1.3 is `restrictedCharFun`, 57.1.) -/
def IsRemovable (Γ : GeneralGame n) (S : Finset (Fin n)) : Prop :=
  ∃ Γ' : GeneralGame n, Γ'.IsZeroSum ∧ Γ'.restrictedCharFun = Γ.restrictedCharFun ∧
    ∀ j ∈ S, Γ'.NoInfluence j

end GeneralGame

/-- Inessentiality of a characteristic function, in the form (57:13) (= (27:C)):
`v(S) = ∑_{k ∈ S} α_k` for all `S ⊆ I`, for a suitable system of constants `α₁, …, αₙ`
("(57:13) is precisely the definition of inessentiality", p. 534). -/
def IsInessential {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∃ α : Fin n → ℝ, ∀ S : Finset (Fin n), v S = ∑ k ∈ S, α k

end TheoryOfGames.GeneralGames
