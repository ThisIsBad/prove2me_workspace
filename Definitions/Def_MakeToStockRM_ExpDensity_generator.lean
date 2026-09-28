import Mathlib

namespace MakeToStockRM.ExpDensity

/-- Partial derivative `∂f/∂x` of `f : ℝ × ℝ → ℝ` at `z = (x, y)`: the Fréchet derivative applied to `(1, 0)`. -/
noncomputable def partialX (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := fderiv ℝ f z (1, 0)

/-- Partial derivative `∂f/∂y` of `f : ℝ × ℝ → ℝ` at `z = (x, y)`: the Fréchet derivative applied to `(0, 1)`. -/
noncomputable def partialY (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := fderiv ℝ f z (0, 1)

/-- The generator `Γ = θ ∂/∂x + (σ²/2) ∂²/∂x² + σδϱ ∂²/∂x∂y + (δ²/2) ∂²/∂y²` of the
inventory/log-price diffusion `(𝒳, 𝒴)` (Caldentey–Wein 2006, p. 865). The mixed partial is
`∂/∂x (∂f/∂y)`. -/
noncomputable def generator (θ σ δ ϱ : ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  θ * partialX f z + σ ^ 2 / 2 * partialX (partialX f) z
    + σ * δ * ϱ * partialX (partialY f) z + δ ^ 2 / 2 * partialY (partialY f) z

/-- The formal adjoint `Γ* = −θ ∂/∂x + (σ²/2) ∂²/∂x² + σδϱ ∂²/∂x∂y + (δ²/2) ∂²/∂y²` of `Γ`
(constant coefficients: only the sign of the first-order term changes). -/
noncomputable def adjointGenerator (θ σ δ ϱ : ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  -θ * partialX f z + σ ^ 2 / 2 * partialX (partialX f) z
    + σ * δ * ϱ * partialX (partialY f) z + δ ^ 2 / 2 * partialY (partialY f) z

end MakeToStockRM.ExpDensity
