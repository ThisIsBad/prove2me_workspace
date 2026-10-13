import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Theorem 1 (p. 7): every characteristic function game `v` has a unique fair allocation rule,
i.e. a unique `Y : GR → ℝ^N` satisfying (7) and (10). -/
theorem theorem_1 {n : ℕ} (hn : 0 < n) (v : Game n) : ∃! Y : Rule n, IsFair v Y := by sorry

end CooperationGraphs.FairRule

