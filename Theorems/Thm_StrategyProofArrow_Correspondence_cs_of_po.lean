import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem cs_of_po {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : StrongProfile ι A → StrongOrder A) (hpo : PO u) :
    CS u := by sorry

end StrategyProofArrow.Correspondence

