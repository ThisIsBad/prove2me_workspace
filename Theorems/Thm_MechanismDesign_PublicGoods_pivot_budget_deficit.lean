import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Lemma 3.8 (p.53): if `N θ̲ < c < N θ̄`, then the ex ante expected budget surplus of
the pivot mechanism is negative. -/
theorem pivot_budget_deficit {N : ℕ} (S : Setting N)
    (hlow : (N : ℝ) * S.θlo < S.c) (hhigh : S.c < (N : ℝ) * S.θhi) :
    S.pivot.budgetSurplus S < 0 := by sorry

end MechanismDesign.PublicGoods

