import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem optimal_iff_ineq3 {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x) (t : ℝ) :
    IsLpOptimal (d + t • d') (stdPolyhedron A b) x ↔
      ∀ j, alpha A d B j + t * beta A d' B j ≤ 0 := by sorry

end GassSaaty.ParametricPivot

