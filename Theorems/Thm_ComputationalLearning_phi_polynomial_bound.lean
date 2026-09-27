import Definitions.Def_ComputationalLearning_VC

open MeasureTheory


namespace ComputationalLearning

/-- **The polynomial bound on `Φ_d(m)`** (p. 57): for `m ≤ d`, `Φ_d(m) = 2^m`, and for `m ≥ d ≥ 1`,
`Φ_d(m) ≤ (em/d)^d = O(m^d)`. -/
theorem phi_polynomial_bound (d m : ℕ) :
    (m ≤ d → Phi d m = 2 ^ m) ∧
    (1 ≤ d → d ≤ m → (Phi d m : ℝ) ≤ (Real.exp 1 * m / d) ^ d) := by sorry

end ComputationalLearning

