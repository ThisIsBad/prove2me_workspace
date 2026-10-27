import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Theorem 2 (Pólya), p. 819: if `Q₁` is a modular solution to the `n`-Queens problem and `Q₂`
is a solution to the `m`-Queens problem, then `Q₁ + nQ₂` is a solution to the `(n·m)`-Queens
problem. -/
theorem theorem_2 (n m : ℕ) (Q₁ Q₂ : Finset Queen) (h₁ : IsModularSol n Q₁)
    (h₂ : IsNQueensSol m Q₂) : IsNQueensSol (n * m) (sumSet Q₁ (scaleSet n Q₂)) := by sorry

end NQueensComp.NPC

