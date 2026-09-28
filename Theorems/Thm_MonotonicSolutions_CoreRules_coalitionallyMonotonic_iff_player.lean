import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic

namespace MonotonicSolutions.CoreRules

theorem coalitionallyMonotonic_iff_player {n : ℕ} (φ : Game n → Fin n → ℝ) :
    IsCoalitionallyMonotonic φ ↔
      ∀ (i : Fin n) (v w : Game n), (∀ S : Finset (Fin n), i ∈ S → w.1 S ≤ v.1 S) →
        (∀ S : Finset (Fin n), i ∉ S → v.1 S = w.1 S) → φ w i ≤ φ v i := by sorry

end MonotonicSolutions.CoreRules

