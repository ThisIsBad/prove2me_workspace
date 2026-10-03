import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData

namespace ProcessingNetworks.GlobalStability

/-- The fluid model of a queueing network under a non-idling policy: Eqs. (8.20)-(8.23) plus the
non-idling condition (8.42) (Eq. 6.7 specialized to `b = e`, kept general in `b` here), restated
from mission VI's `IsNonIdlingSolution`. -/
def IsNonIdlingSolution {I K : ℕ} (dat : QueueingNetworkData I K)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) : Prop :=
  IsFluidModelSolutionQN dat Dh Fh Th Zh ∧
  ∀ (k : Fin K) (t : ℝ), 0 < t → 0 < ∑ i ∈ poolBuffers dat k, Zh t i →
    ∀ d : ℝ, HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) d t → d = dat.b k

/-- Definition 8.23 (global stability of a queueing network's fluid model), Dai & Harrison
p. 152 (PDF p. 168): there is `γ > 0` such that every fluid model solution satisfying
(8.20)-(8.23) and (8.42) has `Z(t) = 0` for all `t ≥ γ|Z(0)|`. -/
def FluidModelGloballyStable {I K : ℕ} (dat : QueueingNetworkData I K) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Dh Fh Th Zh : ℝ → Fin I → ℝ), IsNonIdlingSolution dat Dh Fh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.GlobalStability
