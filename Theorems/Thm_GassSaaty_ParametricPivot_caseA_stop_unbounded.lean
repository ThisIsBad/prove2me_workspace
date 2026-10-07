import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem caseA_stop_unbounded {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (hcol : ∀ i, pivotColumn A B s i ≤ 0) :
    ∀ t : ℝ, -alpha A d B s / beta A d' B s < t →
      lpValue (d + t • d') (stdPolyhedron A b) = ⊥ ∧
        ¬ ∃ y, IsLpOptimal (d + t • d') (stdPolyhedron A b) y := by sorry

end GassSaaty.ParametricPivot

