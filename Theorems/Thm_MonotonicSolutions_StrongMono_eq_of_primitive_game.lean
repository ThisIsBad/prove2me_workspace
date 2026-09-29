import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 70, proof of Theorem 2, index 1): if `φ` is a symmetric allocation
procedure satisfying (7) and `v = c_R v_R` for a nonempty coalition `R` and a real `c_R`,
then `φ_i(v) = c_R / |R|` for `i ∈ R` and `φ_i(v) = 0` for `i ∉ R`. The case `c_R = 0` is
the zero game (index 0). -/
theorem eq_of_primitive_game {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hA : IsAllocationProcedure φ) (hS : IsSymmetric φ) (hM : IsMarginal φ)
    (R : Finset (Fin n)) (hR : R.Nonempty) (c : ℝ) (v : Game n)
    (hv : ∀ S : Finset (Fin n), v.1 S = c * unanimity R S) (i : Fin n) :
    φ v i = if i ∈ R then c / R.card else 0 := by sorry

end MonotonicSolutions.StrongMono
