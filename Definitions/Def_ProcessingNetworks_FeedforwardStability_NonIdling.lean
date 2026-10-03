import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData

namespace ProcessingNetworks.FeedforwardStability

/-- The fluid model of a queueing network under a non-idling policy: (6.1)-(6.6) plus the
non-idling condition (6.7), restated from mission IV's `FullyUtilized dat fam (poolBuffers dat k)
k` (there phrased pathwise on a process family; here phrased directly on the fluid-scaled
solution, as Section 8.3's reduced equations (8.20)-(8.23) and the non-idling condition treat
it). -/
def IsNonIdlingSolution {I K : ℕ} (dat : QueueingNetworkData I K)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) : Prop :=
  IsFluidModelSolutionQN dat Dh Fh Th Zh ∧
  ∀ (k : Fin K) (t : ℝ), 0 < t → 0 < ∑ i ∈ poolBuffers dat k, Zh t i →
    ∀ d : ℝ, HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) d t → d = dat.b k

/-- Definition 6.3 (fluid model stability), specialized to the non-idling-policy fluid model. -/
def NonIdlingFluidStable {I K : ℕ} (dat : QueueingNetworkData I K) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Dh Fh Th Zh : ℝ → Fin I → ℝ), IsNonIdlingSolution dat Dh Fh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.FeedforwardStability
