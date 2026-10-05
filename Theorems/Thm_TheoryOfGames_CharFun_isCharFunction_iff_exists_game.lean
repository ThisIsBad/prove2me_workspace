import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame
import Definitions.Def_TheoryOfGames_CharFun_charFun
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

namespace TheoryOfGames.CharFun

/-- 26.2 (with 25.3.1 and 26.1.1): the complete characterization of the characteristic
functions of all zero-sum `n`-person games. A numerical set function `v` on the subsets of
`I = Fin n` is the characteristic function of some zero-sum `n`-person game with finitely many
pure strategies per player if and only if it fulfills (25:3:a)–(25:3:c). -/
theorem isCharFunction_iff_exists_game {n : ℕ} (v : Finset (Fin n) → ℝ) :
    IsCharFunction v ↔ ∃ Γ : ZeroSumGame n, Γ.charFun = v := by sorry

end TheoryOfGames.CharFun

