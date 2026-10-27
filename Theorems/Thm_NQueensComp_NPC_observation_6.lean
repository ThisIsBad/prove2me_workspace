import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Observation 6, p. 822: `Q₁₉` is a solution to the 19-Queens problem; it has no queen on
difference-diagonals `1, 0, −1`; for its queens `(0, 8)` and `(17, 0)` consider `(19, 8)` and
`(17, 19)`: their sum-diagonals (respectively difference-diagonals) are not within `1` of each
other, of `(0, 0)` or of any queen of `Q₁₉`. -/
theorem observation_6 :
    IsNQueensSol 19 Q19 ∧
    (∀ q ∈ Q19, diffDiag q ≠ 1 ∧ diffDiag q ≠ 0 ∧ diffDiag q ≠ -1) ∧
    ((0, 8) ∈ Q19 ∧ (17, 0) ∈ Q19) ∧
    (1 < |((sumDiag (19, 8) : ℕ) : ℤ) - ((sumDiag (17, 19) : ℕ) : ℤ)| ∧
      1 < |diffDiag (19, 8) - diffDiag (17, 19)|) ∧
    ∀ m ∈ ({(19, 8), (17, 19)} : Finset Queen), ∀ p ∈ insert ((0, 0) : Queen) Q19,
      1 < |((sumDiag m : ℕ) : ℤ) - ((sumDiag p : ℕ) : ℤ)| ∧
        1 < |diffDiag m - diffDiag p| := by sorry

end NQueensComp.NPC

