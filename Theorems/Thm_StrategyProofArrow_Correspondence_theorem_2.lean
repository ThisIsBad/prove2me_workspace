import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem theorem_2 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
:
    ∃ lam : {v : StrongProfile ι A → A // StrategyProof v ∧ Set.range v = Set.univ} ≃
        {u : StrongProfile ι A → StrongOrder A // CS u ∧ NNR u ∧ IIA u},
      ∀ v, Underlies (lam v).1 v.1 := by sorry

end StrategyProofArrow.Correspondence

