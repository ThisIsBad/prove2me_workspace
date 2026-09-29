import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 70, proof of Theorem 2): on a game written in the form (9),
`v = ∑_{∅ ≠ R ⊆ N} c_R v_R`, the Shapley value is `Sh_i(v) = ∑_{R : i ∈ R} c_R / |R|`. -/
theorem shapley_eq_sum_of_unanimity_expansion {n : ℕ} (v : Game n)
    (c : Finset (Fin n) → ℝ)
    (hv : ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S)
    (i : Fin n) :
    Supermodularity.Cooperative.ShapleyValue v.1 i =
      ∑ R ∈ Finset.univ.powerset.filter (fun R => i ∈ R), c R / R.card := by sorry

end MonotonicSolutions.StrongMono
