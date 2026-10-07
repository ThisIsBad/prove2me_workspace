import Mathlib

namespace KingmanSubadditive.PositiveMatrices

/-- §2.3, (2.3.1), p. 893 (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899
(1973)): the supermultiplicative property of the diagonal elements of positive matrices,
`[AB]₁₁ ≥ [A]₁₁[B]₁₁`.

**Formalization Note.** The paper's index `1` is `0 : Fin k` (so `k ≥ 1`, via `NeZero k`).
"Positive" is taken as strictly positive entrywise, as in Theorem 5. -/
theorem supermult_11 {k : ℕ} [NeZero k] (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    A 0 0 * B 0 0 ≤ (A * B) 0 0 := by sorry

end KingmanSubadditive.PositiveMatrices

