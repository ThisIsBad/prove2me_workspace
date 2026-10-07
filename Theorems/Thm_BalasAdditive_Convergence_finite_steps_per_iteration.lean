import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Proof of Convergence Theorem 2, part (a), p. 533. -/
theorem finite_steps_per_iteration {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) :
    ¬ ∃ run : ℕ → State n,
      run 0 = σ ∧
      (∀ t, Step P (run t) (run (t + 1))) ∧
      (∀ t, (run t).history.length = σ.history.length) := by sorry

end BalasAdditive.Convergence

