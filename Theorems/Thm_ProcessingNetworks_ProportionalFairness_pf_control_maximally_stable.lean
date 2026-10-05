import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_MaximalStability

namespace ProcessingNetworks.ProportionalFairness

/-- Corollary 10.16, Dai & Harrison p. 206 (PDF p. 222) — the goal theorem of this mission: the
PF control policy is maximally stable for a unitary network. The book's proof combines Theorem
10.5 (the PF fluid model is stable under the load condition (10.37)), Theorem 6.2 (fluid model
stability implies stability of the network) and Corollary 5.6 (a policy that is stable for every
`λ` in the subcritical region is maximally stable, because by Theorem 5.2 every `λ` for which
some stable policy exists is subcritical). The network-level facts outside this chapter are
explicit hypotheses, as in Corollary 10.17: `Policy` is an abstract type of control policies for
the fixed network shape `(m, P, grp, Ã)`, `PolicyStable p lam` says `p` is a stable policy at
arrival-rate vector `lam` (Section 5.7), `pf` is the PF control policy; `hfluid` is Theorem 6.2
for the PF policy (if the PF fluid model at `lam` is stable then `pf` is a stable policy at
`lam`), and `hnecessary` is Theorem 5.2 in the group-level form of Proposition 10.4 (every `lam`
in the stability region `Λ*` is nonnegative and satisfies the load condition (10.37), with
`alpha lam` the total-arrival-rate vector (2.38) at `lam`). The content established here is that
of Theorem 10.5 on all of the subcritical region, which yields `IsMaximallyStable`. -/
theorem pf_control_maximally_stable
    {I L : ℕ} {Policy : Type*} (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (grp : Fin I → Fin L) (TildeAllocSet : Set (Fin L → ℝ)) (hdom : IsPFDomain TildeAllocSet)
    (alpha : (Fin I → ℝ) → (Fin I → ℝ))
    (halpha : ∀ lam, IsTotalArrivalRates
      (⟨lam, m, hm, P, grp, TildeAllocSet⟩ : PFUnitaryNetworkData I L) (alpha lam))
    (PolicyStable : Policy → (Fin I → ℝ) → Prop) (pf : Policy)
    (hfluid : ∀ lam : Fin I → ℝ,
      PFFluidStable (⟨lam, m, hm, P, grp, TildeAllocSet⟩ : PFUnitaryNetworkData I L) →
        PolicyStable pf lam)
    (hnecessary : ∀ lam ∈ StabilityRegion PolicyStable, (∀ i, 0 ≤ lam i) ∧
      ∃ a ∈ TildeAllocSet, ∀ ℓ, groupAggregate grp (fun i => alpha lam i * m i) ℓ < a ℓ) :
    IsMaximallyStable PolicyStable pf := by sorry

end ProcessingNetworks.ProportionalFairness

