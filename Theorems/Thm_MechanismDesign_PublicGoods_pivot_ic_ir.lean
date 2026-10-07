import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Lemma 3.6 (p.51): the pivot mechanism (Definition 3.8) is incentive-compatible and
individually rational. -/
theorem pivot_ic_ir {N : ℕ} (S : Setting N) :
    S.pivot.IsIC S ∧ S.pivot.IsIR S := by sorry

end MechanismDesign.PublicGoods

