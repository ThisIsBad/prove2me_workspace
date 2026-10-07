import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem rounding_algorithm_approx (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (LB0 UB0 : ℝ) (hLB0 : 0 < LB0)
    (hLB0_le : ∀ q, IsTPath I T q → LB0 ≤ pathLen I q) (N : ℕ)
    (hstop : (roundingRun I T ε LB0 UB0 N).2 ≤ 2 * (roundingRun I T ε LB0 UB0 N).1)
    (p : List ℕ) (hp : IsRoundingOutput I T ε (roundingRun I T ε LB0 UB0 N).1 p) :
    ∀ q, IsTPath I T q → (pathLen I p : ℝ) ≤ (1 + ε) * pathLen I q := by sorry

end HassinRSP.Rounding

