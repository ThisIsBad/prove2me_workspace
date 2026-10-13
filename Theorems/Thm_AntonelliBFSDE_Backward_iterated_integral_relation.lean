import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Proof of Theorem 2.4, p. 780: for a nondecreasing right-continuous path `a` with `a(0) = 0`,
the iterated integrals `a^{(n)}` and `a^{(n-)}` satisfy
`∑_{i=0}^n (-1)^i a_t^{((n-i)-)} a_t^{(i)} = 0` for every `n ≥ 1` and every `t`. -/
theorem iterated_integral_relation (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * iterIntMinus a (n - i) t * iterInt a i t = 0 := by sorry

end AntonelliBFSDE.Backward

