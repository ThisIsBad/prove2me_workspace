import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_NonIdling

namespace ProcessingNetworks.FeedforwardStability

/-- Lemma 8.15, Dai & Harrison p. 145 (PDF p. 161): consider a queueing network operating under a
non-idling policy. For each station `k`, whenever `∑_{i∈I(k)} Zᵢ(t) > 0`,
`d/dt Wₖ(Z(t)) = ρₖ - bₖ`, where `ρₖ := Wₖ(λ)`. -/
theorem workload_derivative_nonidling
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hni : IsNonIdlingSolution dat Dh Fh Th Zh)
    (k : Fin K) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ poolBuffers dat k, Zh t i) :
    ∀ d : ℝ, HasDerivAt (fun s => workloadOperator dat Q (Zh s) k) d t →
      d = workloadOperator dat Q dat.lam k - dat.b k := by sorry

end ProcessingNetworks.FeedforwardStability
