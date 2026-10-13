import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 2, p. 12: for every graph `g` and coalition `T`,
`T/g = ⋃_{S ∈ N/g} (T ∩ S)/g`. -/
theorem quot_eq_biUnion {n : ℕ} (hn : 0 < n) (g : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (hT : T.Nonempty) :
    quot T g = (quot univ g).biUnion (fun S => quot (T ∩ S) g) := by sorry

end CooperationGraphs.FairRule

