import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Theorem 6 (p. 271), size-free: for all `k ≥ 1`, (1) every subcover choosable by C2 on an
input of `EC(k)` has measure at most `(1 + ln k) · F*`; (2) `1 + ln k ≤ Σ_{j=1}^k 1/j + 1/2`;
(3) some input of `EC(k)` with `F* > 0` has a choosable subcover of measure at least
`(Σ_{j=1}^k 1/j) · F*`. -/
theorem overlapGreedy_exactCover_ratio (k : ℕ) (hk : 1 ≤ k) :
    (∀ (α : Type) [DecidableEq α] (F : Input α), InEC k F →
      ∀ M, Choosable F M → (F.measure M : ℝ) ≤ (1 + Real.log k) * (F.opt : ℝ)) ∧
    1 + Real.log k ≤ (harmonic k : ℝ) + 1 / 2 ∧
    (∃ F : Input (ℕ × ℕ), InEC k F ∧ 0 < F.opt ∧
      ∃ M, Choosable F M ∧ (harmonic k : ℝ) * (F.opt : ℝ) ≤ (F.measure M : ℝ)) := by sorry

end JohnsonApprox.ExactCover

