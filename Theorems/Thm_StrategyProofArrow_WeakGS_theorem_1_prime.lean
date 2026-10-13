import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic

namespace StrategyProofArrow.WeakGS

/-- **Theorem 1'** (Satterthwaite, p. 43). Consider a committee in which indifference is admissible
on ballots, with `n ≥ 2` individuals and `m ≥ p ≥ 3`, where `p` is the number of alternatives in the
range `T_p` of the voting procedure `v` over all ballot sets `π^n_m`. If `v` is strategy-proof, then
it is dictatorial. -/
theorem theorem_1_prime {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (v : VotingProcedure ι A)
    (hp : 3 ≤ (Set.range v).ncard) :
    StrategyProof v → Dictatorial v := by sorry

end StrategyProofArrow.WeakGS

