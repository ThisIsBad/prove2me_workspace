import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem group_problem_periodic {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) :
    ∀ i : Fin m,
      (∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y) ∧
        groupValues B N cB cN (b + fun r => B r i) = groupValues B N cB cN b := by sorry

end GomoryGroup.Rel

