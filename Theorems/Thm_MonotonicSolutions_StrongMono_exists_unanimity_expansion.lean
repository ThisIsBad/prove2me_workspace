import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Eq. (9) of Young (1985, p. 70), quoting Shapley: every game `v` (with `v ∅ = 0`) is a
linear combination of primitive games, `v = ∑_{∅ ≠ R ⊆ N} c_R v_R`, where
`v_R(S) = 1` if `R ⊆ S` and `0` otherwise. -/
theorem exists_unanimity_expansion {n : ℕ} (v : Game n) :
    ∃ c : Finset (Fin n) → ℝ, ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S := by sorry

end MonotonicSolutions.StrongMono
