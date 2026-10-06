import Mathlib

namespace GallegoOzerADI.ZeroSetup

/-- Definition 2 (Gallego–Özer 2001, p. 1349). A function `f : ℝ × ℝⁿ → ℝ`, written in curried
form `f x θ`, has *decreasing differences in `(x, θ)`* if
`f(x₁, θ) − f(x₂, θ) ≤ f(x₁, θ') − f(x₂, θ')` for all `x₁ ≥ x₂` and `θ ≥ θ'`,
where `θ ≥ θ'` is the componentwise order on `ℝⁿ = Fin n → ℝ`. -/
def DecreasingDifferences {n : ℕ} (f : ℝ → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (x₁ x₂ : ℝ) (θ θ' : Fin n → ℝ), x₂ ≤ x₁ → θ' ≤ θ →
    f x₁ θ - f x₂ θ ≤ f x₁ θ' - f x₂ θ'

end GallegoOzerADI.ZeroSetup
