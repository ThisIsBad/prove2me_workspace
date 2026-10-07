import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 263, Theorem (Section 2). If `Ax ≤ b` is consistent and `F_n`, `F_m` satisfy
(3), there is a constant `c > 0` such that for every `x` there is a solution `x₀` with
`F_n(x - x₀) ≤ c F_m((Ax - b)⁺)`. The constant is chosen before `x`. -/
theorem hoffman_theorem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty)
    (Fn : (Fin n → ℝ) → ℝ) (Fm : (Fin m → ℝ) → ℝ)
    (hFn : IsPosHomogeneous Fn) (hFm : IsPosHomogeneous Fm) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      Fn (x - x₀) ≤ c * Fm (posPartVec (A *ᵥ x - b)) := by sorry

end HoffmanBound.ErrorBound

