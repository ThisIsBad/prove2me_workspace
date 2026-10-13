import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic

namespace StrategyProofArrow.WeakGS

/-- **Theorem 1 (Gibbard–Satterthwaite)** (Satterthwaite, p. 11). For a strict committee with
`n ≥ 1` individuals and `m ≥ p ≥ 3`, where `p` is the number of alternatives in the range of the
strict voting procedure `ν`, `ν` is strategy-proof if and only if it is dictatorial. -/
theorem theorem_1 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (ν : StrictVotingProcedure ι A)
    (hp : 3 ≤ (Set.range ν).ncard) :
    StrictStrategyProof ν ↔ StrictDictatorial ν := by sorry

end StrategyProofArrow.WeakGS

