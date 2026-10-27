import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 17, p. 827: for an instance `M₄ = ⟨n, C, R, D⁻, D⁺⟩` of Problem 4 and `M₃` its image
under Definition 16, if `S₄` is a solution to `M₄` then `S₃ = (S₄ + (3n − 2, 0)) ∪ Q_{D⁻} ∪ Q_{D⁺}`
is a solution to `M₃`. -/
theorem lemma_17 (M : Inst4) (hM : M.Valid) (S₄ : Finset Queen) (hS : M.IsSol S₄) :
    (def16 M).IsSol (lemma17_map M S₄) := by sorry

end NQueensComp.NPC

