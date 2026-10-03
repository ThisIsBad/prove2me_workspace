import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Remark 9.2.2, p. 203: for `k ≥ 2`, `E[Y^k] < ∞` if and only if
`∑_y y^{k-1} F*(y) < ∞`. -/
theorem moment_finite_iff_tail (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (k : ℕ) (hk : 2 ≤ k) :
    moment u k < ∞ ↔ ∑' y : ℕ, (y : ℝ≥0∞) ^ (k - 1) * tail u y < ∞ := by sorry

end SennottDP.ResidualLife
