import Mathlib

namespace ClarkeGradients.Shared

/-- Clarke (1975), §1, p. 247: `f : ℝⁿ → ℝ` is *locally Lipschitz* in the paper's sense,
i.e. for each bounded subset `B` of `ℝⁿ` there is a constant `K` with
`|f x₁ - f x₂| ≤ K |x₁ - x₂|` for all `x₁, x₂ ∈ B`. -/
def LipschitzOnBounded {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
    ∃ K : NNReal, LipschitzOnWith K f B

end ClarkeGradients.Shared
