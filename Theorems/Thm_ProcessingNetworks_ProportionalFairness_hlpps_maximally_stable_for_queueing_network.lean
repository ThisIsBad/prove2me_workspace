import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_BWSAndQueueing
import Definitions.Def_ProcessingNetworks_ProportionalFairness_MaximalStability

namespace ProcessingNetworks.ProportionalFairness

/-- Corollary 10.18, Dai & Harrison p. 207 (PDF p. 223): the HLPPS control policy is stable for
any subcritical queueing network, and hence HLPPS is maximally stable for a queueing network.
HLPPS coincides with PF control specialized to `grp := server` and the box
`Ã := ∏_k [0, b_k]` (Eq. 10.78, `HLPPSFluidStable`), so the statement is Corollary 10.16 for that
specialization, with the same network-level facts as explicit hypotheses: `hfluid` (Theorem 6.2
together with Proposition 4.4's identification of the HLPPS network with its head-of-line model:
if the HLPPS fluid model at `lam` is stable then `hlpps` is a stable policy at `lam`) and
`hnecessary` (Theorem 5.2 with Proposition 5.1: every `lam` in the stability region is
nonnegative and satisfies the standard load condition `ρ < b`, `ρ_k = ∑_{i : server i = k} αᵢ mᵢ`,
with `alpha lam` the total-arrival-rate vector (2.38) at `lam`). -/
theorem hlpps_maximally_stable_for_queueing_network
    {I K : ℕ} {Policy : Type*} (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (server : Fin I → Fin K) (b : Fin K → ℝ) (hb : ∀ k, 0 < b k)
    (alpha : (Fin I → ℝ) → (Fin I → ℝ))
    (halpha : ∀ lam, IsTotalArrivalRates
      (⟨lam, m, hm, P, server, {y : Fin K → ℝ | ∀ k, 0 ≤ y k ∧ y k ≤ b k}⟩ :
        PFUnitaryNetworkData I K) (alpha lam))
    (PolicyStable : Policy → (Fin I → ℝ) → Prop) (hlpps : Policy)
    (hfluid : ∀ lam : Fin I → ℝ,
      HLPPSFluidStable (⟨lam, m, hm, P, server, b, hb⟩ : QueueingNetworkDataHL I K) →
        PolicyStable hlpps lam)
    (hnecessary : ∀ lam ∈ StabilityRegion PolicyStable, (∀ i, 0 ≤ lam i) ∧
      ∀ k, groupAggregate server (fun i => alpha lam i * m i) k < b k) :
    IsMaximallyStable PolicyStable hlpps := by sorry

end ProcessingNetworks.ProportionalFairness

