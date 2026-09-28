import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 71, proof of Theorem 2): let `φ` be symmetric and
`v = ∑_{∅ ≠ R ⊆ N} c_R v_R`. If players `i` and `j` both belong to every coalition `R ≠ ∅`
with `c_R ≠ 0` (i.e. to the common core `∩_k R_k` of the expression), then
`φ_i(v) = φ_j(v)`. -/
theorem eq_on_common_core {n : ℕ} (φ : Game n → Fin n → ℝ) (hS : IsSymmetric φ)
    (v : Game n) (c : Finset (Fin n) → ℝ)
    (hv : ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S)
    (i j : Fin n) (hij : ∀ R : Finset (Fin n), R.Nonempty → c R ≠ 0 → i ∈ R ∧ j ∈ R) :
    φ v i = φ v j := by sorry

end MonotonicSolutions.StrongMono
