import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame
import Definitions.Def_TheoryOfGames_CharFun_charFun
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

namespace TheoryOfGames.CharFun

/-- 26.1.1: the converse of 25.3.1. For any numerical set function `v(S)` which fulfills the
conditions (25:3:a)–(25:3:c) there exists a zero-sum `n`-person game `Γ` (finitely many pure
strategies per player) of which this `v(S)` is the characteristic function, i.e. whose
characteristic function agrees with `v` on every subset `S` of `I`. -/
theorem exists_game_of_isCharFunction {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) : ∃ Γ : ZeroSumGame n, Γ.charFun = v := by sorry

end TheoryOfGames.CharFun

