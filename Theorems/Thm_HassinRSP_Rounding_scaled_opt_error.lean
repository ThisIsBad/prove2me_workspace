import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem scaled_opt_error (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (LB : ℝ) (hLB : 0 < LB) (p : List ℕ) (hp : IsRoundingOutput I T ε LB p) :
    ∀ q, IsTPath I T q → (pathLen I p : ℝ) ≤ pathLen I q + ε * LB := by sorry

end HassinRSP.Rounding

