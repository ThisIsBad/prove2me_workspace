import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game

namespace MonotonicSolutions.CoreRules

/-- Coalitional monotonicity, Young 1985, p. 68, Eq. (4): if `v T ≥ w T` for some coalition `T`
(any `T ⊆ N`, including `N` itself) and `v S = w S` for every `S ≠ T`, then
`φ v i ≥ φ w i` for every `i ∈ T`. -/
def IsCoalitionallyMonotonic {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (v w : Game n) (T : Finset (Fin n)), w.1 T ≤ v.1 T → (∀ S, S ≠ T → v.1 S = w.1 S) →
    ∀ i ∈ T, φ w i ≤ φ v i

end MonotonicSolutions.CoreRules
