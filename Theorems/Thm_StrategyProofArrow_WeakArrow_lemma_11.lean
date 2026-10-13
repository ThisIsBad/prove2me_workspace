import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Lemma 11**, Satterthwaite p. 48: let `u` be a social welfare function on weak ballot sets,
with `n ≥ 2` and `m ≥ 3`, and let `μ(B) = γ[u(B)]` break the ties of each social ordering by a
regular tie-breaker with tie-breaking order `Q`. If `u` satisfies CS, NNR and IIA, then `μ` has
range contained in the strong orders and satisfies CS, NNR and IIA. -/
theorem lemma_11 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A) (Q : StrongOrder A)
    (hCS : CS u) (hNNR : NNR u) (hIIA : IIA u) :
    (∀ B, (breakTies Q (u B)).1.IsStrong) ∧
      CS (fun B => (breakTies Q (u B)).1) ∧
      NNR (fun B => (breakTies Q (u B)).1) ∧
      IIA (fun B => (breakTies Q (u B)).1) := by sorry

end StrategyProofArrow.WeakArrow

