import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Lemma 7, p. 823: if `n ≡ 1 (mod 6)` or `n ≡ 5 (mod 6)` then `Aₙ` and `Bₙ` are modular
solutions to the `n`-Queens problem, and they use the same set of sum-diagonals and the same set of
difference-diagonals. -/
theorem lemma_7 (n : ℕ) (hn : n % 6 = 1 ∨ n % 6 = 5) :
    IsModularSol n (A n) ∧ IsModularSol n (B n) ∧
      (A n).image sumDiag = (B n).image sumDiag ∧
      (A n).image diffDiag = (B n).image diffDiag := by sorry

end NQueensComp.NPC

