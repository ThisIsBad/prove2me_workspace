import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model
import Definitions.Def_HoffmanBound_ErrorBound_NormConstants

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 265, (9). If `Ax ≤ b` is consistent and all `A_i · A_j > 0`, then with
`v = min_{i,j} A_i · A_j` and `a = max_{i,j} |a_ij|`, every `x` has a solution `x₀` with
`|x - x₀| ≤ (a / v) |(Ax - b)⁺|` (max norms). -/
theorem eq9 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) (hpos : ∀ i j, 0 < A i ⬝ᵥ A j) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ aMax A / vMin A * maxNorm (posPartVec (A *ᵥ x - b)) := by sorry

end HoffmanBound.ErrorBound

