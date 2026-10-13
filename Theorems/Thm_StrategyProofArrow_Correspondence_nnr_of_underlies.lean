import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem nnr_of_underlies {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v)
    (u : StrongProfile ι A → StrongOrder A) (hu : Underlies u v) (hpo : PO u) (hiia : IIA u) :
    NNR u := by sorry

end StrategyProofArrow.Correspondence

