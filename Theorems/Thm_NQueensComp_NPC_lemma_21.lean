import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 21, p. 830: for a non-empty instance `M₅ = {M₄,ₐ | 0 ≤ a < k}` of Problem 5 and `M₄`
its image under Definition 20, if `S₅ = {S₄,ₐ}` is a solution to `M₅` then
`S₄ = ⋃_{0≤a<k} (S₄,ₐ + (αₐ, βₐ))` is a solution to `M₄`. -/
theorem lemma_21 (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms ≠ []) (Ss : List (Finset Queen))
    (hS : Inst5IsSol Ms Ss) : (def20 Ms).IsSol (lemma21_map Ms Ss) := by sorry

end NQueensComp.NPC

