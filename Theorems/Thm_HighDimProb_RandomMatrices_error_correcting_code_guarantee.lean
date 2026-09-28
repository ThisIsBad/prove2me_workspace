import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_hammingDist
import Definitions.Def_HighDimProb_RandomMatrices_IsErrorCorrectingCode

namespace HighDimProb.RandomMatrices

/-- **Theorem 4.3.5** (Guarantees for an error correcting code), Vershynin, *High-Dimensional
Probability* (2018), p. 88.

Assume that positive integers `k, n, r` are such that `n ≥ k + 2r log₂(en/(2r))`. Then there
exists an error correcting code that encodes `k`-bit strings into `n`-bit strings and can
correct `r` errors. -/
theorem error_correcting_code_guarantee (k n r : ℕ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r)
    (h : (n : ℝ) ≥ (k : ℝ) + 2 * (r : ℝ) * Real.logb 2 (Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))) :
    ∃ E : (Fin k → Bool) → (Fin n → Bool), ∃ D : (Fin n → Bool) → (Fin k → Bool),
      IsErrorCorrectingCode (r := r) E D := by sorry

end HighDimProb.RandomMatrices
