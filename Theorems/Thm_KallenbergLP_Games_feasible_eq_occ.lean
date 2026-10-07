import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.4 (ii) (p. 198): under Assumptions 6.2.1 and 6.2.2, with `β ≫ 0`, if `(x, z)` is
feasible for (6.2.2) and `π_{ia} := x_{ia} / ∑_a x_{ia}`, then `π` is a stationary decision rule
for player I, `x = x(π)` and `z ≤ z(π)`. -/
theorem feasible_eq_occ {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (x : Fin N → α → ℝ) (z : Fin N → ℝ) (hxz : LP622Feasible G β' x z) :
    IsDecisionRule1 G (piOfX G x) ∧ x = occ G β' (piOfX G x) ∧ z ≤ zval G β' (piOfX G x) := by sorry

end KallenbergLP.Games

