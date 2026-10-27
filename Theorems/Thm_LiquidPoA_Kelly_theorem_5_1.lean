import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Theorem 5.1, p. 14: the full liquid price of anarchy of Kelly is exactly two. -/
theorem theorem_5_1 (n : ℕ) (hn : 2 ≤ n) :
    lpoa (kelly n) = 2 := by sorry

end LiquidPoA.Kelly

