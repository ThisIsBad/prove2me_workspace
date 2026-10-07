import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Lemma 3.7 (p.52): no incentive-compatible and individually rational direct mechanism
that implements the first best decision rule `q*` has a larger ex ante expected budget surplus
(revenue minus cost) than the pivot mechanism. -/
theorem pivot_max_budget_surplus {N : ℕ} (S : Setting N) (M : DirectMechanism N)
    (hM : M.IsDirect S) (hIC : M.IsIC S) (hIR : M.IsIR S)
    (hq : ∀ θ ∈ S.typeSpace, M.q θ = S.qStar θ) :
    M.budgetSurplus S ≤ S.pivot.budgetSurplus S := by sorry

end MechanismDesign.PublicGoods

