import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix

namespace MakeToStockRM.ExpDensity

open Matrix

/-- The conormal flux `(Σ w) · ∇f(z)`, with `Σ = covMatrix σ δ ϱ` and `∇f = (∂f/∂x, ∂f/∂y)`; that is,
`(σ² w₁ + σδϱ w₂) ∂f/∂x + (σδϱ w₁ + δ² w₂) ∂f/∂y`. -/
noncomputable def conormalFlux (σ δ ϱ : ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (w : ℝ × ℝ) : ℝ :=
  (covMatrix σ δ ϱ *ᵥ ![w.1, w.2]) ⬝ᵥ ![partialX f z, partialY f z]

/-- The boundary integral `∫_{∂Ω} (Σ n⃗) · ∇f · p dl` over the four pieces (35) of `∂Ω`, with `n⃗`
the inward unit normal and `n⃗ dl` written out in the parametrization of each piece:
`(1, −η'(y)) dy` on `x = η(y)`, `(−1, ξ'(y)) dy` on `x = ξ(y)`, `(0, 1) dx` on `y = y_min`,
`(0, −1) dx` on `y = y_max`. -/
noncomputable def boundaryTerm (σ δ ϱ : ℝ) (η ξ : ℝ → ℝ) (ymin ymax : ℝ)
    (f p : ℝ × ℝ → ℝ) : ℝ :=
  (∫ y in ymin..ymax, conormalFlux σ δ ϱ f (η y, y) (1, -deriv η y) * p (η y, y))
    + (∫ y in ymin..ymax, conormalFlux σ δ ϱ f (ξ y, y) (-1, deriv ξ y) * p (ξ y, y))
    + (∫ x in η ymin..ξ ymin, conormalFlux σ δ ϱ f (x, ymin) (0, 1) * p (x, ymin))
    + (∫ x in η ymax..ξ ymax, conormalFlux σ δ ϱ f (x, ymax) (0, -1) * p (x, ymax))

end MakeToStockRM.ExpDensity
