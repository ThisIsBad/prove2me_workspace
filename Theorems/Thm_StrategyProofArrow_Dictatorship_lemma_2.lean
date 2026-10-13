import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 2** (Satterthwaite, p. 15). For a strict committee with one individual and three
alternatives, and `1 ≤ p ≤ 3`, a strategy-proof strict voting procedure is either fully
dictatorial or strong alternative-excluding. -/
theorem lemma_2 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : Fintype.card ι = 1) (hm : Fintype.card A = 3)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    FullyDictatorial f ∨ StrongAltExcluding f := by sorry

end StrategyProofArrow.Dictatorship

