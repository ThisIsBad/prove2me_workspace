import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_NonIdling

namespace ProcessingNetworks.FeedforwardStability

/-- Corollary 8.19, Dai & Harrison p. 148 (PDF p. 164): a generalized Jackson network is a
queueing network with a one-to-one correspondence between classes and server pools
(`dat.p` bijective, so `I = K` and each pool serves exactly one class — HLSPS then reduces to
non-idling FCFS, since `γ ≡ 1`). If the standard load condition `ρ < b` holds, the fluid model is
stable under the non-idling FCFS policy. -/
theorem generalized_jackson_stable
    {I K : ℕ} (dat : QueueingNetworkData I K) (hgj : Function.Bijective dat.p)
    (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse dat.P Q)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    NonIdlingFluidStable dat := by sorry

end ProcessingNetworks.FeedforwardStability
