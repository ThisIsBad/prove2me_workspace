import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem below_lambdaBar_violates_ineq3_prime {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    ∀ t : ℝ, t < -alpha A d B s / beta A d' B s →
      ¬ ∀ j, alpha A d B' j + t * beta A d' B' j ≤ 0 := by sorry

end GassSaaty.ParametricPivot

