import Mathlib
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Rule
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Loss

namespace RobbinsSeqDesign.ForcedSampling

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm

/-- Robbins (1952), Section 2, Eq. (16), p. 532: for any two populations A, B such that
`α`, `β` exist (are finite) and any pair of sequences (13), the loss (9) of the rule `R̄`
tends to zero: `lim_{n→∞} L_n(A, B, R̄) = 0`. -/
theorem forced_sampling_loss_tendsto_zero (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    Tendsto (fun n : ℕ => loss ν (rule σ) n) atTop (𝓝 0) := by sorry

end RobbinsSeqDesign.ForcedSampling

