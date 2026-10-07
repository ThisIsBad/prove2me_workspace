import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem marketGame_isBalancedGame {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) : IsBalancedGame (marketGame A) := by sorry

end ShapleyScarf.Balanced

