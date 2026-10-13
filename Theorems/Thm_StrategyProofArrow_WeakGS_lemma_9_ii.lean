import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic

namespace StrategyProofArrow.WeakGS

/-- **Lemma 9, second sentence** (Satterthwaite, p. 41). In a committee (`n ≥ 1`, `m ≥ 3`), if the
voting procedure `v` is strategy-proof, then there exist a strict strategy-proof voting procedure
`ν` and a tie-breaking function `α` (not necessarily regular) with `v(B) = ν[α(B)]` for all
`B ∈ π^n_m`. -/
theorem lemma_9_ii {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : VotingProcedure ι A) (hv : StrategyProof v) :
    ∃ (ν : StrictVotingProcedure ι A) (α : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A),
      StrictStrategyProof ν ∧ IsTieBreaking α ∧ ∀ B : WeakProfile ι A, v B = ν (α B) := by sorry

end StrategyProofArrow.WeakGS

