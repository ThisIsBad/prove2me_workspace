import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_Removable

namespace TheoryOfGames.GeneralGames

/-- (57:B), 57.4.1: every one-element set `S = (k)` is removable (in the sense of (57:A)) in
every zero-sum `n`-person game `Γ`. -/
theorem singleton_removable {n : ℕ} (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) (k : Fin n) :
    Γ.IsRemovable {k} := by sorry

end TheoryOfGames.GeneralGames

