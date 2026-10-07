import Mathlib
import Definitions.Def_LawlerMoore_FunctionalEq_Problem
import Definitions.Def_LawlerMoore_FunctionalEq_Recursion

namespace LawlerMoore.FunctionalEq

/-- Eq. (1) (p. 77): for every `j ≤ n` and every integer `t`, the value `f(j, t)` given by the
recursion (1) is the minimum total loss of the first `j` jobs, over all mode assignments and
all feasible timings (idle time allowed, start at time `0`) in which job `j` is completed no
later than time `t`: it is `+∞` exactly when no such timing exists, and otherwise it is a
real number that is attained and is at most every such total loss. No assumption is made on
the losses `α`, `β`. -/
theorem eq1_value {n : ℕ} (a b : Fin n → ℕ) (α β : Fin n → ℕ → ℝ) (j : ℕ) (hj : j ≤ n)
    (t : ℤ) :
    (f a b α β j t = ⊤ ↔ lossesBy a b α β j t = ∅) ∧
      ∀ x : ℝ, f a b α β j t = (x : WithTop ℝ) → IsLeast (lossesBy a b α β j t) x := by sorry

end LawlerMoore.FunctionalEq

