import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem lemma_8 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v) (hrange : Set.range v = Set.univ) :
    ∃! u : StrongProfile ι A → StrongOrder A, Underlies u v ∧ CS u ∧ NNR u ∧ IIA u := by sorry

end StrategyProofArrow.Correspondence

