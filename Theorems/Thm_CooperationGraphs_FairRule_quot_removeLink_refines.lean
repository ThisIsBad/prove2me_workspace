import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 3, p. 13: `S/(g \ a,b)` refines `S/g` as a partition of `S`, and
`S/(g \ a,b) = S/g` if `a ∉ S`. -/
theorem quot_removeLink_refines {n : ℕ} (hn : 0 < n) (g : SimpleGraph (Fin n)) (a b : Fin n)
    (hab : g.Adj a b) (S : Finset (Fin n)) (hS : S.Nonempty) :
    (∀ B ∈ quot S (removeLink g a b), ∃ C ∈ quot S g, B ⊆ C) ∧
      (a ∉ S → quot S (removeLink g a b) = quot S g) := by sorry

end CooperationGraphs.FairRule

