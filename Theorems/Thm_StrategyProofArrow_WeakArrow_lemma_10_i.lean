import Mathlib
import Definitions.Def_StrategyProofArrow_WeakArrow_Basic

namespace StrategyProofArrow.WeakArrow

/-- **Lemma 10, first sentence**, Satterthwaite p. 44: let `u` be a social welfare function on weak
ballot sets with range contained in the strong orders. If `u(B) = μ(γ(B))` for every `B`, where
`γ` is a regular tie-breaking function and `μ` is a strict social welfare function satisfying IIA,
CS and NNR, then `u` satisfies IIA, CS and NNR. (The printed `u^{nm}(B) = u^{nm}[γ(B)]` is read as
`μ^{nm}[γ(B)]`, as the proof writes it.) -/
theorem lemma_10_i {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (u : WeakProfile ι A → WeakOrder A) (hrange : ∀ B, (u B).IsStrong)
    (γ : WeakProfile ι A → StrongProfile ι A) (hγ : IsRegular γ)
    (μ : StrongProfile ι A → StrongOrder A)
    (hIIA : StrictIIA μ) (hCS : StrictCS μ) (hNNR : StrictNNR μ)
    (hu : ∀ B, u B = (μ (γ B)).1) :
    IIA u ∧ CS u ∧ NNR u := by sorry

end StrategyProofArrow.WeakArrow

