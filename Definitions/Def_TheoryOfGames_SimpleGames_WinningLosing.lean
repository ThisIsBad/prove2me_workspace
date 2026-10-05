import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Solution

namespace TheoryOfGames.SimpleGames

/-- 31.1.4, (31:3): a set `S` of players is *flat* if `v(S) = ∑_{k in S} v((k))`. -/
def IsFlat {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : Prop :=
  v S = ∑ k ∈ S, v {k}

/-- (49:L), 49.1.2: `L_Γ` is the set of all flat sets `S (⊆ I)` — the losing coalitions. -/
def losingSets {n : ℕ} (v : Finset (Fin n) → ℝ) : Set (Finset (Fin n)) :=
  {S | IsFlat v S}

/-- (49:W), 49.1.2: `W_Γ` is the set of all sets `S (⊆ I)` for which `-S` is flat — the
winning coalitions. -/
def winningSets {n : ℕ} (v : Finset (Fin n) → ℝ) : Set (Finset (Fin n)) :=
  {S | IsFlat v Sᶜ}

/-- 49.4: an essential game which fulfills (49:1:b) `W_Γ ∪ L_Γ = Ī` (every subset of `I`
is winning or losing) is called *simple*. -/
def IsSimple {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ¬ IsInessential v ∧ ∀ S : Finset (Fin n), S ∈ winningSets v ∨ S ∈ losingSets v

/-- 49.6.3: the *minimal* elements of a system `W` of sets — those `S` of `W` of which no proper
subset belongs to `W`; for `W = W_Γ` their set is `W^m_Γ`, the minimal winning coalitions. -/
def minimalSets {n : ℕ} (W : Set (Finset (Fin n))) : Set (Finset (Fin n)) :=
  {S | S ∈ W ∧ ∀ T : Finset (Fin n), T ⊂ S → T ∉ W}

/-- (49:W*), 49.6.2: the properties characterizing the systems `W (⊆ Ī)` of winning
coalitions of simple games:
* (49:W*:a) of two complements (in `I`) `S`, `-S`, one and only one belongs to `W`;
* (49:W*:b) `W` contains the supersets of its elements;
* (49:W*:c) `W` contains `I` and all `(n - 1)`-element sets. -/
def SatisfiesWStar {n : ℕ} (W : Set (Finset (Fin n))) : Prop :=
  (∀ S : Finset (Fin n), (S ∈ W ↔ Sᶜ ∉ W)) ∧
  (∀ S T : Finset (Fin n), S ∈ W → S ⊆ T → T ∈ W) ∧
  (Finset.univ ∈ W ∧ ∀ S : Finset (Fin n), S.card + 1 = n → S ∈ W)

end TheoryOfGames.SimpleGames
