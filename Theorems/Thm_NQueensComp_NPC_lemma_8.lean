import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Lemma 8 (Rivin and Zabih), p. 823, corrected: if `Q` is a solution to the `n`-Queens
problem, `P ⊆ Q`, and `P₁` is a set of queens with `|P₁| = |P|` (added; the printed lemma is false
without it) that uses the same sets of rows, columns, sum-diagonals and difference-diagonals as `P`,
then `(Q \ P) ∪ P₁` is a solution to the `n`-Queens problem. -/
theorem lemma_8 (n : ℕ) (Q P P₁ : Finset Queen) (hQ : IsNQueensSol n Q) (hPQ : P ⊆ Q)
    (hcard : P₁.card = P.card)
    (hrow : P₁.image row = P.image row) (hcol : P₁.image col = P.image col)
    (hsum : P₁.image sumDiag = P.image sumDiag) (hdiff : P₁.image diffDiag = P.image diffDiag) :
    IsNQueensSol n ((Q \ P) ∪ P₁) := by sorry

end NQueensComp.NPC

