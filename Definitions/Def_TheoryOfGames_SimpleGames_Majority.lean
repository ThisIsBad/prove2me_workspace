import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

namespace TheoryOfGames.SimpleGames

/-- (50:1), 50.1.2: for numerical weights `w₁, …, wₙ`, `W` is the set of all those `S` which
contain a majority of total weight: `∑_{i in S} wᵢ > ½ ∑_{i=1}^n wᵢ`. -/
def weightedW {n : ℕ} (w : Fin n → ℝ) : Set (Finset (Fin n)) :=
  {S | (1 / 2 : ℝ) * ∑ i, w i < ∑ i ∈ S, w i}

/-- (50:B:a) and (50:B:b), 50.1.3: for all `i₀`, `0 ≦ w_{i₀} < ½ ∑_{i=1}^n wᵢ`; and for all
`S ⊆ I`, `∑_{i in S} wᵢ ≠ ½ ∑_{i=1}^n wᵢ`. -/
def SatisfiesB {n : ℕ} (w : Fin n → ℝ) : Prop :=
  (∀ i₀ : Fin n, 0 ≤ w i₀ ∧ w i₀ < (1 / 2 : ℝ) * ∑ i, w i) ∧
  (∀ S : Finset (Fin n), ∑ i ∈ S, w i ≠ (1 / 2 : ℝ) * ∑ i, w i)

/-- (50:6), 50.2.1: `a_S = 2 ∑_{i in S} wᵢ - ∑_{i=1}^n wᵢ = ∑_{i in S} wᵢ - ∑_{i in -S} wᵢ`. -/
def advantage {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  2 * ∑ i ∈ S, w i - ∑ i, w i

/-- (50:E), 50.2.2: the weights `w₁, …, wₙ` are *homogeneous* if the `a_S` of (50:6) have a
common value `a` for all `S` of `W^m` (the minimal elements of the `W` of (50:1)). -/
def IsHomogeneous {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∃ a : ℝ, ∀ S ∈ minimalSets (weightedW w), advantage w S = a

/-- 50.1.3: `w₁, …, wₙ` are weights for the game `v` — the game is the weighted majority game
`[w₁, …, wₙ]`: the weights fulfil (50:B) and the `W` they define by (50:1) is `W_Γ`. -/
def IsWeightsFor {n : ℕ} (v : Finset (Fin n) → ℝ) (w : Fin n → ℝ) : Prop :=
  SatisfiesB w ∧ winningSets v = weightedW w

/-- 50.4.2, 50.5.1: for numbers `x₁, …, xₙ` and a set `S`, the vector `α^S` with
`α^S_i = -1` for `i` not in `S` and `α^S_i = -1 + xᵢ` for `i` in `S`. -/
noncomputable def alphaS {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then -1 + x i else -1

/-- 50.5.1: the set `V` of the `α^S`, `S` in `U`. -/
def mainSet {n : ℕ} (U : Set (Finset (Fin n))) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {α | ∃ S ∈ U, α = alphaS x S}

/-- (50:11), 50.5.2: `R(β)`, the set of all `i` with `βᵢ ≧ -1 + xᵢ`. -/
noncomputable def rSet {n : ℕ} (x : Fin n → ℝ) (β : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => -1 + x i ≤ β i)

/-- (50:G), 50.5.2: `U*` is the set of all `R (⊆ I)` which possess some subset belonging
to `U`. -/
def uStar {n : ℕ} (U : Set (Finset (Fin n))) : Set (Finset (Fin n)) :=
  {R | ∃ T ∈ U, T ⊆ R}

/-- (50:G), 50.5.2: `U⁺` is the set of all `R (⊆ I)` for which `-R` does not belong to `U*`. -/
def uPlus {n : ℕ} (U : Set (Finset (Fin n))) : Set (Finset (Fin n)) :=
  {R | Rᶜ ∉ uStar U}

end TheoryOfGames.SimpleGames
