import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic

namespace StrategyProofArrow.WeakGS

/-- **Lemma 9, first sentence** (Satterthwaite, p. 41). In a committee (`n ≥ 1`, `m ≥ 3`), if
`v(B) = ν[γ(B)]` for all `B ∈ π^n_m`, where `ν` is a strict strategy-proof voting procedure and `γ`
is a regular tie-breaking function, then `v` is strategy-proof. -/
theorem lemma_9_i {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : VotingProcedure ι A) (ν : StrictVotingProcedure ι A)
    (γ : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A)
    (hν : StrictStrategyProof ν) (hγ : IsRegularTieBreaking γ)
    (hv : ∀ B : WeakProfile ι A, v B = ν (γ B)) :
    StrategyProof v := by sorry

end StrategyProofArrow.WeakGS

