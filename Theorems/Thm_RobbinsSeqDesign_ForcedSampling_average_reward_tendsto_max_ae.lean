import Mathlib
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Rule
import Definitions.Def_RobbinsSeqDesign_ForcedSampling_Loss

namespace RobbinsSeqDesign.ForcedSampling

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm

/-- Robbins (1952), Section 2, Eq. (14), p. 532: for any two populations A, B whose
expectations `α`, `β` exist (are finite) and any pair of sequences (13), under the rule `R̄`,
with probability 1, `S_n / n → max(α, β)`. -/
theorem average_reward_tendsto_max_ae (ν : StochasticBandit 2)
    (hint : ∀ i, Integrable id (ν.P i)) (σ : ForcedSchedule) :
    ∀ᵐ ω ∂(banditTrajMeasure ν (rule σ)),
      Tendsto (fun n : ℕ => partialSum n ω / (n : ℝ)) atTop
        (𝓝 (max (banditArmMean ν 0) (banditArmMean ν 1))) := by sorry

end RobbinsSeqDesign.ForcedSampling

