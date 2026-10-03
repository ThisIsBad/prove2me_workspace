import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_BWSAndQueueing

namespace ProcessingNetworks.ProportionalFairness

/-- Corollary 10.17, Dai & Harrison p. 206 (PDF p. 222): if the standard load condition `ρ < b`
holds, a BWS network is stable under PF control; otherwise it is not stable under any control
policy. The book's own proof chains three facts outside this chunk's own apparatus — Proposition
4.4 (a processor-sharing model is stable iff its EHL model is stable) together with the model
translation of Section 4.4 (`hpf`: PF-stability of the BWS network is equivalent to fluid
stability of its EHL-model unitary-network representation, `grp`/`TildeAllocSet`), Proposition 5.1
(standard load condition iff subcriticality, in the group-level form `hload_iff`), and Theorem 5.2
(subcriticality is necessary for any stable policy to exist, `hnecessary`) — each packaged as an
explicit hypothesis, per this series' convention for content structurally outside a chunk's own
scope; the genuine content proved here is deriving the corollary's two-way conclusion from these
together with Corollary 10.16 (`pf_control_maximally_stable`, this chunk's own goal item). -/
theorem pf_maximally_stable_for_bws
    {I K L : ℕ} {Policy : Type*} (PolicyStable : Policy → BWSNetworkData I K → Prop)
    (pf : Policy) (grp : Fin I → Fin L) (TildeAllocSet : Set (Fin L → ℝ))
    (hdom : IsPFDomain TildeAllocSet)
    (hpf : ∀ dat : BWSNetworkData I K,
      PolicyStable pf dat ↔
        PFFluidStable (⟨dat.lam, dat.m, dat.hm, 0, grp, TildeAllocSet⟩ : PFUnitaryNetworkData I L))
    (hload_iff : ∀ dat : BWSNetworkData I K,
      BWSLoadCondition dat ↔
        ∃ a ∈ TildeAllocSet, ∀ ℓ, groupAggregate grp (fun i => dat.lam i * dat.m i) ℓ < a ℓ)
    (hnecessary : ∀ dat : BWSNetworkData I K, ¬ BWSLoadCondition dat → ∀ p, ¬ PolicyStable p dat)
    (dat : BWSNetworkData I K) :
    (BWSLoadCondition dat → PolicyStable pf dat) ∧
    (¬ BWSLoadCondition dat → ∀ p, ¬ PolicyStable p dat) := by sorry

end ProcessingNetworks.ProportionalFairness
