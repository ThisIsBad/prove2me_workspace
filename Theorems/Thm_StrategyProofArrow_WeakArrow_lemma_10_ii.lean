import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Lemma 10, second sentence**, Satterthwaite p. 44: let `u` be a social welfare function on weak
ballot sets with range contained in the strong orders. If `u` satisfies IIA, CS and NNR, then there
exist a tie-breaking function `α` and a strict social welfare function `μ` satisfying IIA, CS and
NNR such that `u(B) = μ(α(B))` for every weak ballot set `B`. -/
theorem lemma_10_ii {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A) (hrange : ∀ B, (u B).IsStrong)
    (hIIA : IIA u) (hCS : CS u) (hNNR : NNR u) :
    ∃ α : WeakProfile ι A → StrongProfile ι A, IsTieBreaking α ∧
      ∃ μ : StrongProfile ι A → StrongOrder A,
        StrictIIA μ ∧ StrictCS μ ∧ StrictNNR μ ∧ ∀ B, u B = (μ (α B)).1 := by sorry

end StrategyProofArrow.WeakArrow

