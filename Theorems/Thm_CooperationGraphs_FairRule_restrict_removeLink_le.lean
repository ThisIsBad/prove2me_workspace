import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 3, p. 13: if `v` is superadditive then `(v/g)_S ≥ (v/(g \ a,b))_S` for every
coalition `S`, with equality if `a ∉ S`. -/
theorem restrict_removeLink_le {n : ℕ} (hn : 0 < n) (v : Game n) (hv : IsSuperadditive v)
    (g : SimpleGraph (Fin n)) (a b : Fin n) (hab : g.Adj a b)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    restrict v (removeLink g a b) S ≤ restrict v g S ∧
      (a ∉ S → restrict v (removeLink g a b) S = restrict v g S) := by sorry

end CooperationGraphs.FairRule

