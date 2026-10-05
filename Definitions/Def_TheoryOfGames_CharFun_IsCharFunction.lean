import Mathlib

namespace TheoryOfGames.CharFun

/-- The conditions (25:3:a)–(25:3:c) of 25.3.1 on a numerical set function `v` defined for all
subsets `S` of `I = Fin n` (`-S` is the complement `Sᶜ`):
* (25:3:a) `v(∅) = 0`;
* (25:3:b) `v(-S) = -v(S)`;
* (25:3:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`.
From 26.2 on the book calls every function satisfying them a *characteristic function*. -/
def IsCharFunction {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S : Finset (Fin n), v Sᶜ = -v S) ∧
  (∀ S T : Finset (Fin n), Disjoint S T → v S + v T ≤ v (S ∪ T))

end TheoryOfGames.CharFun
