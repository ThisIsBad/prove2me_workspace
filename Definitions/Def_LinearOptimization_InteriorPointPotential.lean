import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The primal-dual potential function of §9.3.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §9.3 p. 409: the potential
`G(x, s) = q log s'x − ∑ⱼ log xⱼ − ∑ⱼ log sⱼ` with parameter `q > n`
(`log` = natural logarithm). Used by Bertsimas & Tsitsiklis, Theorem 9.4
(`LinearOptimization.interior_point_potential_reduction`, Mission XII).
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, §9.3 (p. 409).** The primal-dual potential function
`G(x, s) = q log s'x − ∑ⱼ log xⱼ − ∑ⱼ log sⱼ`. -/
noncomputable def interiorPointPotential {n : ℕ} (q : ℝ)
    (x s : Fin n → ℝ) : ℝ :=
  q * Real.log (s ⬝ᵥ x) - ∑ j, Real.log (x j) - ∑ j, Real.log (s j)

end LinearOptimization
