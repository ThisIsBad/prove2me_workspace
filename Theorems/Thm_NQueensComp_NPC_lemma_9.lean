import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Lemma 9, p. 824: let `q₁, q₂` fit on board size `n` and let `q₃, q₄` be any queens.  If the
columns (rows) of `q₃, q₄` differ, so do the columns (rows) of `q₁ + nq₃` and `q₂ + nq₄`; if the
sum-diagonals (difference-diagonals) of `q₃, q₄` differ by more than one, then the sum-diagonals
(difference-diagonals) of `q₁ + nq₃` and `q₂ + nq₄` differ; if all four hold, `q₁ + nq₃` does not
attack `q₂ + nq₄`. -/
theorem lemma_9 (n : ℕ) (q₁ q₂ q₃ q₄ : Queen) (h₁ : FitsOn n q₁) (h₂ : FitsOn n q₂) :
    (col q₃ ≠ col q₄ → col (q₁ + n • q₃) ≠ col (q₂ + n • q₄)) ∧
    (row q₃ ≠ row q₄ → row (q₁ + n • q₃) ≠ row (q₂ + n • q₄)) ∧
    (1 < |((sumDiag q₃ : ℕ) : ℤ) - ((sumDiag q₄ : ℕ) : ℤ)| →
      sumDiag (q₁ + n • q₃) ≠ sumDiag (q₂ + n • q₄)) ∧
    (1 < |diffDiag q₃ - diffDiag q₄| → diffDiag (q₁ + n • q₃) ≠ diffDiag (q₂ + n • q₄)) ∧
    (col q₃ ≠ col q₄ → row q₃ ≠ row q₄ →
      1 < |((sumDiag q₃ : ℕ) : ℤ) - ((sumDiag q₄ : ℕ) : ℤ)| →
      1 < |diffDiag q₃ - diffDiag q₄| → ¬ Attacks (q₁ + n • q₃) (q₂ + n • q₄)) := by sorry

end NQueensComp.NPC

