import Mathlib

namespace TheoryOfGames.SimpleGames

/-- The conditions (25:3:a)–(25:3:c) of 25.3.1 on a numerical set function `v` defined for all
subsets `S` of the set of players `I = Fin n` (the book's players `1, …, n` are `0, …, n - 1`;
`-S` is the complement `Sᶜ`):
* (25:3:a) `v(∅) = 0`;
* (25:3:b) `v(-S) = -v(S)`;
* (25:3:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`.
These are the standing properties of the characteristic function of a zero-sum `n`-person game. -/
def IsCharFunction {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S : Finset (Fin n), v Sᶜ = -v S) ∧
  (∀ S T : Finset (Fin n), Disjoint S T → v S + v T ≤ v (S ∪ T))

/-- 30.1.1: an *imputation* is a vector `α = {α₁, …, αₙ}` with (30:1) `αᵢ ≧ v((i))` for
`i = 1, …, n` and (30:2) `∑ᵢ αᵢ = 0`. -/
def IsImputation {n : ℕ} (v : Finset (Fin n) → ℝ) (α : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, v {i} ≤ α i) ∧ ∑ i, α i = 0

/-- 30.1.1, (30:3): a set `S` of players is *effective* for `α` if `∑_{i in S} αᵢ ≦ v(S)`. -/
def IsEffective {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) (α : Fin n → ℝ) : Prop :=
  ∑ i ∈ S, α i ≤ v S

/-- 30.1.1, (30:4): `α` *dominates* `β`, `α ⊱ β`, if there exists a set `S` with
(30:4:a) `S` is not empty, (30:4:b) `S` is effective for `α`, (30:4:c) `αᵢ > βᵢ` for all `i`
in `S`. (The book applies the relation to imputations; every statement using it restricts
`α`, `β` to imputations.) -/
def Dominates {n : ℕ} (v : Finset (Fin n) → ℝ) (α β : Fin n → ℝ) : Prop :=
  ∃ S : Finset (Fin n), S.Nonempty ∧ IsEffective v S α ∧ ∀ i ∈ S, β i < α i

/-- 30.1.1, (30:5): a set `V` of imputations is a *solution* if
(30:5:a) no `β` in `V` is dominated by an `α` in `V`, and
(30:5:b) every imputation `β` not in `V` is dominated by some `α` in `V`. -/
def IsSolution {n : ℕ} (v : Finset (Fin n) → ℝ) (V : Set (Fin n → ℝ)) : Prop :=
  (∀ α ∈ V, IsImputation v α) ∧
  (∀ α ∈ V, ∀ β ∈ V, ¬ Dominates v α β) ∧
  (∀ β : Fin n → ℝ, IsImputation v β → β ∉ V → ∃ α ∈ V, Dominates v α β)

/-- 27.1.4, (27:2) with (27:4): the *reduced form* of `v`,
`v̄(S) = v(S) + ∑_{k in S} α⁰ₖ` with `α⁰ₖ = -v((k)) + (1/n) ∑_{j=1}^n v((j))`. -/
noncomputable def reducedForm {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  v S + ∑ k ∈ S, (-v {k} + (1 / (n : ℝ)) * ∑ j, v {j})

/-- 27.3.1: a game with characteristic function `v` is *inessential* if its reduced form is
`v̄(S) ≡ 0`; it is *essential* (27.3.2) otherwise, i.e. when `¬ IsInessential v`. -/
def IsInessential {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), reducedForm v S = 0

end TheoryOfGames.SimpleGames
