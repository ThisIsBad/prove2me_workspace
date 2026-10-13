import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 2, p. 13: the rule `g ↦ φ(v/g)` satisfies the equity condition (10):
`φ_a(v/g) − φ_b(v/g) = φ_a(v/(g \ a,b)) − φ_b(v/(g \ a,b))` for every link `a,b ∈ g`. -/
theorem shapley_restrict_isEquitable {n : ℕ} (hn : 0 < n) (v : Game n) :
    IsEquitable (fun g => shapley (restrict v g)) := by sorry

end CooperationGraphs.FairRule

