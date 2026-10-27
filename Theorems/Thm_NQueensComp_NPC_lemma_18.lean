import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 18, p. 827: for an instance `M₄` of Problem 4 and `M₃` its image under Definition 16,
if `S₃` is a solution to `M₃` then `S₄ = {(α − 3n + 2, β) | (α, β) ∈ S₃, β < n}` is a solution to
`M₄`. -/
theorem lemma_18 (M : Inst4) (hM : M.Valid) (S₃ : Finset Queen) (hS : (def16 M).IsSol S₃) :
    M.IsSol (lemma18_map M S₃) := by sorry

end NQueensComp.NPC

