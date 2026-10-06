import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

open MeasureTheory

/-- Manuscript p. 13: in the mates game with `1 ≤ m ≤ M`, against every randomized on-line
algorithm `K` there is an adaptive off-line adversary `Q` (it sets `r₂` to the mate of `a₁`)
whose expected cost is `1` while the algorithm's expected cost is `M`. -/
theorem offline_forces_ratio (t : ℕ) [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (Ω : Type) [MeasurableSpace Ω] (K : RandAlg (Fin t × Bool) (Fin t × Bool) Ω) :
    ∃ Q : OfflineAdv (Fin t × Bool) (Fin t × Bool),
      ∫ ω, algCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = M ∧
      ∫ ω, advCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = 1 := by sorry

end OnlineRandomization.Tightness

