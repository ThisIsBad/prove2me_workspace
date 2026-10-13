import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Proof of Theorem 2.4, p. 783: for a nondecreasing right-continuous path `a` with `a(0) = 0`,
`a_t^{(n-)} ≤ a_t^n / n!` for every `n` and every `t`. -/
theorem iterIntMinus_le_pow_div_factorial (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0)
    (n : ℕ) (t : ℝ≥0) :
    iterIntMinus a n t ≤ a t ^ n / (n.factorial : ℝ) := by sorry

end AntonelliBFSDE.Backward

