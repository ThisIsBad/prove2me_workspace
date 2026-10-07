import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem ip_feasible_group_feasible {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    ∀ (xB : Fin m → ℕ) (xN : Fin n → ℕ),
      IsIPFeasible B N b xB xN → IsGroupFeasible B N b xN := by sorry

end GomoryGroup.Rel

