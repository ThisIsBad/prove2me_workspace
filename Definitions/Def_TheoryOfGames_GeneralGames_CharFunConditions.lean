import Mathlib

namespace TheoryOfGames.GeneralGames

/-- The conditions (57:1:a)–(57:1:c) of 57.2.1 on a numerical set function `v` on all subsets
`S` of `Ī = (1, …, n, n + 1) = Fin (n + 1)` (`⊥S` is the complement `Ī - S = Sᶜ`):
* (57:1:a) `v(∅) = 0`;
* (57:1:b) `v(⊥S) = -v(S)`;
* (57:1:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`.
From 57.3.4 on the book calls such functions *extended characteristic functions*. -/
def IsExtendedCharFunction {n : ℕ} (v : Finset (Fin (n + 1)) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S : Finset (Fin (n + 1)), v Sᶜ = -v S) ∧
  (∀ S T : Finset (Fin (n + 1)), Disjoint S T → v S + v T ≤ v (S ∪ T))

/-- The conditions (57:2:a), (57:2:c) of 57.2.1 on a numerical set function `v` on all subsets
`S` of `I = (1, …, n) = Fin n`:
* (57:2:a) `v(∅) = 0`;
* (57:2:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`.
From 57.3.4 on the book calls such functions *restricted characteristic functions*. -/
def IsRestrictedCharFunction {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S T : Finset (Fin n), Disjoint S T → v S + v T ≤ v (S ∪ T))

end TheoryOfGames.GeneralGames
