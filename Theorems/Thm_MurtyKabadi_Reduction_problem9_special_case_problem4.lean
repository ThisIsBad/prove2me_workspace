import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem problem9_special_case_problem4 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ) :
    (∀ y s : Fin n → ℝ, f5 d d0 δ ε y s = Q (mkMatrix d d0 δ ε) (Sum.elim y s)) ∧
    ((∃ p ∈ P n, f5 d d0 δ ε p.1 p.2 < 0) ↔ Problem4 (mkMatrix d d0 δ ε) n) := by sorry

end MurtyKabadi.Reduction
