import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.6 (p.48): for every direct mechanism that is ex ante budget balanced
(Definition 3.6) there is an equivalent (Definition 3.7) direct mechanism that is ex post budget
balanced (Definition 3.5). -/
theorem exAnte_budget_balance_to_exPost {N : ℕ} (S : Setting N) (M : DirectMechanism N)
    (hM : M.IsDirect S) (hBB : M.IsExAnteBB S) :
    ∃ M' : DirectMechanism N, M'.IsDirect S ∧ M.Equivalent S M' ∧ M'.IsExPostBB S := by sorry

end MechanismDesign.PublicGoods

