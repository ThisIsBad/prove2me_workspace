import Mathlib
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Rule
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Loss

namespace RobbinsSeqDesign.ForcedSampling

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm

/-- Robbins (1952), Section 2, Eq. (15), p. 532: for any two populations A, B whose
expectations `α`, `β` exist (are finite) and any pair of sequences (13), under the rule `R̄`,
`E(S_n / n) → max(α, β)`. -/
theorem expected_average_tendsto_max (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    Tendsto (fun n : ℕ => ∫ ω, partialSum n ω / (n : ℝ) ∂(banditTrajMeasure ν (rule σ)))
      atTop (𝓝 (max (banditArmMean ν 0) (banditArmMean ν 1))) := by sorry

end RobbinsSeqDesign.ForcedSampling

