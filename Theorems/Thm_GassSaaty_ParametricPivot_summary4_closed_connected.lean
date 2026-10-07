import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem summary4_closed_connected {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x) :
    IsClosed {t : ℝ | ∃ y, IsLpOptimal (d + t • d') (stdPolyhedron A b) y} ∧
      IsPreconnected {t : ℝ | ∃ y, IsLpOptimal (d + t • d') (stdPolyhedron A b) y} := by sorry

end GassSaaty.ParametricPivot

