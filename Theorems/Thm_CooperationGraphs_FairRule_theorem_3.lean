import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Theorem 3 (p. 8): if `v` is superadditive, then the fair allocation rule for `v` is totally
stable. -/
theorem theorem_3 {n : ℕ} (hn : 0 < n) (v : Game n) (hv : IsSuperadditive v) (Y : Rule n) (hY : IsFair v Y) :
    IsTotallyStable Y := by sorry

end CooperationGraphs.FairRule

