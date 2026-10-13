import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Theorem 1, printed p. 8, with the explicit count from its proof. -/
theorem theorem_1 {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (t : ℝ) (x s : ℕ → Fin n → ℝ)
    (hinit : N2 A b c (1 / 4) (x 0) (s 0))
    (hgap : x 0 ⬝ᵥ s 0 ≤ (2 : ℝ) ^ t)
    (hrun : ∀ k : ℕ, (2 : ℝ) ^ (-t) < x k ⬝ᵥ s k →
      Alg1Step A b c (x k) (s k) (x (k + 1)) (s (k + 1))) :
    ∃ k : ℕ,
      k ≤ ⌈2 * Real.log 2 * (8 : ℝ) ^ (1 / 4 : ℝ) *
        Real.sqrt (n : ℝ) * t⌉₊ ∧
      x k ⬝ᵥ s k ≤ (2 : ℝ) ^ (-t) := by sorry

end AdaptiveStepIPM.PredCorr

