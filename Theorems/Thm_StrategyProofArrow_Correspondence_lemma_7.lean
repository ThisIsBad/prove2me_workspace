import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem lemma_7 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : StrongProfile ι A → StrongOrder A) (hcs : CS u) (hnnr : NNR u) (hiia : IIA u) :
    (∃ v : StrongProfile ι A → A, Underlies u v) ∧
      ∀ v : StrongProfile ι A → A, Underlies u v →
        StrategyProof v ∧ Set.range v = Set.univ := by sorry

end StrategyProofArrow.Correspondence

