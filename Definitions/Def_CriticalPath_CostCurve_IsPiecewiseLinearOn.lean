import Mathlib

namespace CriticalPath.CostCurve

/-- `f` is piecewise linear on `S ⊆ ℝ` with finitely many pieces: there are breakpoints
`β 0 < β 1 < ⋯ < β m` with `S ⊆ [β 0, ∞)` and slopes/intercepts `σ k, ι k` such that on
`S ∩ [β k, β (k+1)]` (and on `S ∩ [β m, ∞)` for the last piece) `f x = σ k * x + ι k`.
The pieces cover all of `S`. -/
def IsPiecewiseLinearOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ (m : ℕ) (β σ ι : Fin (m + 1) → ℝ), StrictMono β ∧ S ⊆ Set.Ici (β 0) ∧
    ∀ (k : Fin (m + 1)) (x : ℝ), x ∈ S → β k ≤ x → (∀ k', k < k' → x ≤ β k') →
      f x = σ k * x + ι k

end CriticalPath.CostCurve
