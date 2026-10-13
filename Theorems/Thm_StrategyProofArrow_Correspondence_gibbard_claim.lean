import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem gibbard_claim {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v) (hrange : Set.range v = Set.univ)
    (Q : StrongOrder A) :
    ∃ μ : StrongProfile ι A → StrongOrder A,
      (∀ B x y, (μ B).1.rel x y ↔ gibbardRel v Q B x y) ∧
      Underlies μ v ∧ PO μ ∧ IIA μ := by sorry

end StrategyProofArrow.Correspondence

