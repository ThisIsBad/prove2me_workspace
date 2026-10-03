import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_HLSPS

namespace ProcessingNetworks.FeedforwardStability

/-- Theorem 8.18, Dai & Harrison p. 148 (PDF p. 164) — the goal theorem of this mission: consider
a queueing network subject to relaxed control, with `γ` the proportion vector of (8.30). If the
standard load condition `ρ < b` holds, then the fluid model corresponding to the HLSPS control
policy with proportion vector `γ` is stable, and thus, by Theorem 6.2, the queueing network is
also stable under that HLSPS control policy. Every class is assumed to have a positive total
arrival rate `αᵢ > 0` (`hα_pos`): the proportions `γᵢ = αᵢmᵢ/ρₖ` of (8.30) are only defined for
`ρₖ > 0`, and the proof's `ε := min (bₖ/ρₖ - 1) αⱼ` is positive only when every `αⱼ > 0` (a class
with `αⱼ = 0` would receive the proportion `γⱼ = 0` and never be served). -/
theorem hlsps_fluid_model_stable
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (hα_pos : ∀ i : Fin I, 0 < totalArrivalRates dat Q i)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    HLSPSFluidStable dat Q := by sorry

end ProcessingNetworks.FeedforwardStability
