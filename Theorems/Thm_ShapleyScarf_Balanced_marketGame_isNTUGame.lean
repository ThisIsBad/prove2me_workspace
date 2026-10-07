import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_NTUGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem marketGame_isNTUGame {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) : IsNTUGame (marketGame A) := by sorry

end ShapleyScarf.Balanced

