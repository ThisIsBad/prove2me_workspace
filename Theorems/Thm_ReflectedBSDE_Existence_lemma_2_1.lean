import Mathlib
import Definitions.Def_ReflectedBSDE_Existence_Skorohod

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedBSDE.Existence

/-- Lemma 2.1 (the Skorohod lemma, pp. 704–705): for a continuous `x : [0, ∞[ → ℝ` with
`x_0 ≥ 0` there is exactly one pair `(y, k)` solving the Skorohod problem, and its `k` is
`k_t = sup_{s≤t} x_s⁻`. -/
theorem lemma_2_1 (x : ℝ≥0 → ℝ) (hx : Continuous x) (hx0 : 0 ≤ x 0) :
    (∃! p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ), IsSkorohodSolution x p.1 p.2) ∧
    ∀ y k : ℝ≥0 → ℝ, IsSkorohodSolution x y k →
      ∀ t, k t = ⨆ s : Iic t, max (-(x s)) 0 := by sorry

end ReflectedBSDE.Existence

