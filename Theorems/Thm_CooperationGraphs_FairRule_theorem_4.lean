import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Theorem 4 (p. 10): every game `w` in graph function form has a unique fair allocation rule
`Y : GR → ℝ^N`, i.e. a unique `Y` satisfying the efficiency condition (14) and the equity
condition (10). -/
theorem theorem_4 {n : ℕ} (hn : 0 < n) (G : GraphFunctionGame n) :
    ∃! Y : Rule n, IsEfficientGF G Y ∧ IsEquitable Y := by sorry

end CooperationGraphs.FairRule

