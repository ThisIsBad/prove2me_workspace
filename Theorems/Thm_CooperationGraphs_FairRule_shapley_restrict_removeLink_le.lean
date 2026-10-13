import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 3, p. 13: if `v` is superadditive then `φ_a(v/g) − φ_a(v/(g \ a,b)) ≥ 0`. -/
theorem shapley_restrict_removeLink_le {n : ℕ} (hn : 0 < n) (v : Game n) (hv : IsSuperadditive v)
    (g : SimpleGraph (Fin n)) (a b : Fin n) (hab : g.Adj a b) :
    shapley (restrict v (removeLink g a b)) a ≤ shapley (restrict v g) a := by sorry

end CooperationGraphs.FairRule

