import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem nash_support_minimizes {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (s : Fin m → ℝ)
    (p : Fin n → Fin m → ℝ) (hp : IsNash w s p) :
    (∀ i j, 0 < p i j → ∀ j', linkCost w s p i j ≤ linkCost w s p i j') ∧
      ∀ i, expCost w s p i = Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) := by sorry

end WorstCaseEq.Speeds

