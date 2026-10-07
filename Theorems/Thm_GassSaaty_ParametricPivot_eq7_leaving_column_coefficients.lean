import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem eq7_leaving_column_coefficients {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ)
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (s : Fin n) (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    alpha A d B' (B ℓ) = -alpha A d B s / pivotColumn A B s ℓ ∧
      beta A d' B' (B ℓ) = -beta A d' B s / pivotColumn A B s ℓ := by sorry

end GassSaaty.ParametricPivot

