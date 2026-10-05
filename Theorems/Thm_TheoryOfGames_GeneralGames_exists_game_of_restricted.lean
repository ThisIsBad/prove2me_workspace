import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- 57.3.1: the necessary conditions (57:2:a), (57:2:c) are also sufficient. For any numerical
set function `v(S)` (`S ⊆ I`) which fulfills (57:2:a), (57:2:c) there exists a general
`n`-person game `Γ` (finitely many pure strategies per player) of which this `v(S)` is the
restricted characteristic function. -/
theorem exists_game_of_restricted {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsRestrictedCharFunction v) :
    ∃ Γ : GeneralGame n, Γ.restrictedCharFun = v := by sorry

end TheoryOfGames.GeneralGames

