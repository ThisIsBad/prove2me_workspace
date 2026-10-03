import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator

namespace ProcessingNetworks.FeedforwardStability

/-- `γ`, Eq. (8.30): for `i ∈ I(k)`, `γᵢ := αᵢmᵢ/ρₖ`, where `α` is the total-arrival-rate vector
and `ρₖ = W_k(λ)` is station `k`'s load. -/
noncomputable def proportionVector {I K : ℕ} (dat : QueueingNetworkData I K)
    (Q : Matrix (Fin I) (Fin I) ℝ) (i : Fin I) : ℝ :=
  (totalArrivalRates dat Q i * dat.m i) / workloadOperator dat Q dat.lam (dat.p i)

/-- Definition 8.17 (the HLSPS fluid model), Dai & Harrison p. 148 (PDF p. 164): the fluid
equations (6.1)-(6.6) together with (7.21) for the HLSPS policy function, which allocates each
pool's capacity among its classes in the fixed proportions `γ` (Eq. 8.30): whenever `Zᵢ(t) > 0`,
`Ṫᵢ(t) = b_{p(i)} γᵢ`. -/
def IsHLSPSSolution {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) : Prop :=
  IsFluidModelSolutionQN dat Dh Fh Th Zh ∧
  ∀ (i : Fin I) (t : ℝ), 0 < t → 0 < Zh t i →
    ∀ d : ℝ, HasDerivAt (fun s => Th s i) d t → d = dat.b (dat.p i) * proportionVector dat Q i

/-- Definition 6.3 (fluid model stability), specialized to the HLSPS fluid model with proportion
vector `γ` induced by `dat`, `Q`. -/
def HLSPSFluidStable {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ) :
    Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Dh Fh Th Zh : ℝ → Fin I → ℝ), IsHLSPSSolution dat Q Dh Fh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.FeedforwardStability
