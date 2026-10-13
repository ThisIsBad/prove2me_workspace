import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Theorem 1 (Gibbard–Satterthwaite)** (Satterthwaite, p. 11). For a strict committee with
`n ≥ 1` individuals whose strict voting procedure has a range `T_p` of `p ≥ 3` alternatives
(so `m ≥ p ≥ 3`), the procedure is strategy-proof if and only if it is dictatorial: some
individual always obtains their most preferred alternative of the range. -/
theorem theorem_1 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι)
    (f : (ι → A → A → Prop) → A) (hp : 3 ≤ (range f).ncard) :
    IncentiveCompatible f ↔ Dictatorial f := by sorry

end StrategyProofArrow.Dictatorship

