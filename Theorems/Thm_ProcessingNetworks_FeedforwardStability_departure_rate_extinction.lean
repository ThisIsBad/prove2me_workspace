import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator

namespace ProcessingNetworks.FeedforwardStability

open Matrix

/-- Lemma 8.20, Dai & Harrison p. 148 (PDF p. 164) (not listed in `BRIEF.md`'s disposition table
but numbered and within this chunk's page range — added as a milestone, see `STATUS.md`): fix
`ε > 0`. If a fluid model solution `(D,F,T,Z)` of a queueing network satisfies (6.1)-(6.6) and
`Zⱼ(t) > 0` implies `Ḋⱼ(t) ≥ αⱼ + ε` (8.31), then `Z(t) = 0` for
`t ≥ |(I-P')⁻¹Z(0)|/ε`. This is the key structural lemma behind Theorem 8.18's proof. -/
theorem departure_rate_extinction
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hsol : IsFluidModelSolutionQN dat Dh Fh Th Zh)
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ (j : Fin I) (t : ℝ), 0 < t → 0 < Zh t j →
      ∀ d : ℝ, HasDerivAt (fun s => Dh s j) d t → totalArrivalRates dat Q j + ε ≤ d) :
    ∀ t : ℝ, (∑ i, (Q.mulVec (Zh 0)) i) / ε ≤ t → Zh t = fun _ => 0 := by sorry

end ProcessingNetworks.FeedforwardStability
