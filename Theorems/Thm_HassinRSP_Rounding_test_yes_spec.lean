import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem test_yes_spec (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) :
    testYes I T ε V → ∀ q, IsTPath I T q → V ≤ pathLen I q := by sorry

end HassinRSP.Rounding

