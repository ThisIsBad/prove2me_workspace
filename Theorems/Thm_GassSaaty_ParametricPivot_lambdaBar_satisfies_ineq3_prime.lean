import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem lambdaBar_satisfies_ineq3_prime {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    ∀ j, alpha A d B' j + (-alpha A d B s / beta A d' B s) * beta A d' B' j ≤ 0 := by sorry

end GassSaaty.ParametricPivot

