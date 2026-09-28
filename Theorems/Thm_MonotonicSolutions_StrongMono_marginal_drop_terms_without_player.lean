import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 71, proof of Theorem 2): if `v = ∑_{∅ ≠ R ⊆ N} c_R v_R` and
`w = ∑_{R : i ∈ R} c_R v_R` keeps only the terms whose coalition contains `i`, then
`w^i(S) = v^i(S)` for every coalition `S`. -/
theorem marginal_drop_terms_without_player {n : ℕ} (c : Finset (Fin n) → ℝ) (i : Fin n)
    (S : Finset (Fin n)) :
    marginal (fun T => ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty ∧ i ∈ R),
        c R * unanimity R T) i S =
      marginal (fun T => ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R T) i S := by sorry

end MonotonicSolutions.StrongMono
