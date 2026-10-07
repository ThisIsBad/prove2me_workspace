import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.2 (p. 193): under Assumption 6.2.1, `val(TMG)` is the smallest TMG-superharmonic
vector. -/
theorem value_smallest_superharmonic {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) :
    ∃ y : Fin N → ℝ, IsValueOfGame G y ∧
      IsLeast {y' : Fin N → ℝ | TMGSuperharmonic G y'} y := by sorry

end KallenbergLP.Games

