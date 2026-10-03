import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), Proposition 9.2.1, p. 202: for `Y` on `{1, 2, …}` with tail `F*`,
`E[Y] = ∑_{y=0}^∞ F*(y)` and, for `k ≥ 2`,
`E[Y^k] = 1 + ∑_{z=0}^{k-1} C(k,z) [∑_{y=1}^∞ y^z F*(y)]` (9.4). -/
theorem moments_via_tail (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) :
    moment u 1 = ∑' y, tail u y ∧
    ∀ k : ℕ, 2 ≤ k →
      moment u k = 1 + ∑ z ∈ Finset.range k,
        (Nat.choose k z : ℝ≥0∞) * ∑' y : ℕ, (if 1 ≤ y then (y : ℝ≥0∞) ^ z * tail u y else 0) := by sorry

end SennottDP.ResidualLife
