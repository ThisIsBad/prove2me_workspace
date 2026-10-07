import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem test_no_spec (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) :
    testNo I T ε V → ∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) < V * (1 + ε) := by sorry

end HassinRSP.Rounding

