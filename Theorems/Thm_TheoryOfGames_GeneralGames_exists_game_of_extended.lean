import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- 57.3.3: the necessary conditions (57:1:a)–(57:1:c) are also sufficient. For any numerical
set function `v(S)` (`S ⊆ Ī = (1, …, n, n + 1)`) which fulfills (57:1:a)–(57:1:c) there
exists a general `n`-person game `Γ` of which this `v(S)` is the extended characteristic
function. -/
theorem exists_game_of_extended {n : ℕ} (v : Finset (Fin (n + 1)) → ℝ)
    (hv : IsExtendedCharFunction v) :
    ∃ Γ : GeneralGame n, Γ.extCharFun = v := by sorry

end TheoryOfGames.GeneralGames

