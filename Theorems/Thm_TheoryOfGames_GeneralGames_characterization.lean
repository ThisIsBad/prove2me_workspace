import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

namespace TheoryOfGames.GeneralGames

/-- 57.3.4 (with 57.2.1, 57.3.1–57.3.3): the complete mathematical characterizations of both
the restricted and the extended characteristic functions of all possible general `n`-person
games `Γ`. A numerical set function `v` on the subsets of `I = (1, …, n)` is the restricted
characteristic function of some general `n`-person game iff it fulfills (57:2:a), (57:2:c);
a numerical set function on the subsets of `Ī = (1, …, n, n + 1)` is the extended
characteristic function of some general `n`-person game iff it fulfills (57:1:a)–(57:1:c). -/
theorem characterization (n : ℕ) :
    (∀ v : Finset (Fin n) → ℝ,
        IsRestrictedCharFunction v ↔ ∃ Γ : GeneralGame n, Γ.restrictedCharFun = v) ∧
      (∀ v : Finset (Fin (n + 1)) → ℝ,
        IsExtendedCharFunction v ↔ ∃ Γ : GeneralGame n, Γ.extCharFun = v) := by sorry

end TheoryOfGames.GeneralGames

