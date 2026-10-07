import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model
import Definitions.Def_HoffmanBound_ErrorBound_NormConstants

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 265, (8). If `Ax ≤ b` is consistent, every `x` has a solution `x₀` with
`|x - x₀| ≤ c |(Ax - b)⁺|` (max norms), where `c = max_{v_S > 0} a_S / v_S` over the nonempty sets
`S` of rows, `a_S` as in (6) and `v_S` the game value (7). -/
theorem eq8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ constC8 A * maxNorm (posPartVec (A *ᵥ x - b)) := by sorry

end HoffmanBound.ErrorBound

