import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem rounding_run_bounds (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (LB0 UB0 : ℝ) (hLB0 : 0 < LB0)
    (hLB0_le : ∀ q, IsTPath I T q → LB0 ≤ pathLen I q) (k : ℕ) :
    0 < (roundingRun I T ε LB0 UB0 k).1 ∧
    (∀ q, IsTPath I T q → (roundingRun I T ε LB0 UB0 k).1 ≤ pathLen I q) ∧
    ((∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) ≤ UB0) →
      ∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) ≤ (roundingRun I T ε LB0 UB0 k).2) := by sorry

end HassinRSP.Rounding

