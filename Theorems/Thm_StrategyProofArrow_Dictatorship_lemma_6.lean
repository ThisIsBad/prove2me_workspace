import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 6** (Satterthwaite, p. 26). For a strict committee with `n ≥ 2`, `m ≥ 3` and
`p ≥ 1` (`m ≥ p` holds automatically), if `f` is strategy-proof and the strict ballot sets `C`,
`D` satisfy `θ_T(C_i) = θ_T(D_i)` for every individual `i`, where `T = T_p` is the range, then
`f C = f D`. -/
theorem lemma_6 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f)
    (C D : ι → A → A → Prop) (hC : IsPrefProfile C) (hD : IsPrefProfile D)
    (hCD : ∀ i, AgreeOn (range f) (C i) (D i)) :
    f C = f D := by sorry

end StrategyProofArrow.Dictatorship

