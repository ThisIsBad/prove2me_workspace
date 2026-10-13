import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 1** (Satterthwaite, p. 13). For a strict committee with `n ≥ 1`, `m ≥ 3` and
`p ≥ 1`, every strategy-proof strict voting procedure satisfies Condition U. -/
theorem lemma_1 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    ConditionU f := by sorry

end StrategyProofArrow.Dictatorship

