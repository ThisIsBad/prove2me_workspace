import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model
import Definitions.Def_HoffmanBound_ErrorBound_NormConstants

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 265, (10). If `Ax ≤ b` is consistent and
`w = min_i (g_ii + ∑_{j : g_ij < 0} g_ij) > 0` for the Gram matrix `g_ij = A_i · A_j` of all rows,
then with `a = max_{i,j} |a_ij|` every `x` has a solution `x₀` with
`|x - x₀| ≤ (a / w) ‖(Ax - b)⁺‖` (max norm on the left, sum norm on the right). -/
theorem eq10 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) (hw : 0 < wConst A) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ aMax A / wConst A * sumNorm (posPartVec (A *ᵥ x - b)) := by sorry

end HoffmanBound.ErrorBound

