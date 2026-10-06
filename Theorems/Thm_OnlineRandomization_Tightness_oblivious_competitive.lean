import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

/-- Manuscript p. 12: if `m, M ≥ 1` and `β = ((2t − 2)m + M + 1)/(2t)`, the uniform algorithm
`G` is `β`-competitive (ratio `x ↦ β·x`) against any oblivious adversary in the mates game. -/
theorem oblivious_competitive (t : ℕ) [NeZero t] (m M β : ℝ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (hβ : β = ((2 * (t : ℝ) - 2) * m + M + 1) / (2 * (t : ℝ))) :
    IsCompetitiveObl (matesGame t m M) (fun x => β * x) (unifAlg t) := by sorry

end OnlineRandomization.Tightness

