import Mathlib
import Definitions.Def_ManneJobShop_Formulation_Model

namespace ManneJobShop.Formulation

/-- Manne (1960), p. 221, formulation (2)–(7): for an instance with at least one task, an integer
`t₀` is the least `t` for which the integer program (2)–(7) is solvable iff `t₀` is the least
make-span `max_j (x_j + a_j)` over all schedules. -/
theorem integer_program_optimum_eq_min_makespan {n : ℕ} [NeZero n] (I : Instance n) (t₀ : ℤ) :
    IsLeast {t : ℤ | ∃ x y, IsIPFeasible I x y t} t₀ ↔
      IsLeast (makespan I '' {x | IsSchedule I x}) t₀ := by sorry

end ManneJobShop.Formulation

