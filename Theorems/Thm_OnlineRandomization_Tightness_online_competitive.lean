import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

/-- Manuscript pp. 12–13: if `1 ≤ m ≤ M`, `α = (1 + (2t − 1)M)/(2 + (2t − 2)m)` and
`α(m − 1) ≤ M − m`, the uniform algorithm `G` is `α`-competitive (ratio `x ↦ α·x`) against
any adaptive on-line adversary in the mates game. -/
theorem online_competitive (t : ℕ) [NeZero t] (m M α : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hα : α = (1 + (2 * (t : ℝ) - 1) * M) / (2 + (2 * (t : ℝ) - 2) * m))
    (hgap : α * (m - 1) ≤ M - m) :
    IsCompetitiveOnline (matesGame t m M) (fun x => α * x) (unifAlg t) := by sorry

end OnlineRandomization.Tightness

