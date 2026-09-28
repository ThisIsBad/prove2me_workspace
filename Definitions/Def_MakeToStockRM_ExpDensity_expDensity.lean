import Mathlib

namespace MakeToStockRM.ExpDensity

/-- The exponent `m_x = 2θ / (σ²(1 − ϱ²))` of (47) (Caldentey–Wein 2006, p. 867). -/
noncomputable def mx (θ σ ϱ : ℝ) : ℝ := 2 * θ / (σ ^ 2 * (1 - ϱ ^ 2))

/-- The exponent `m_y = −2ϱθ / (σδ(1 − ϱ²))` of (47) (Caldentey–Wein 2006, p. 867). -/
noncomputable def my (θ σ δ ϱ : ℝ) : ℝ := -2 * ϱ * θ / (σ * δ * (1 - ϱ ^ 2))

/-- The unnormalized exponential density `(x, y) ↦ exp(m_x x + m_y y)` of Proposition 2. -/
noncomputable def expDensity (θ σ δ ϱ : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (mx θ σ ϱ * z.1 + my θ σ δ ϱ * z.2)

end MakeToStockRM.ExpDensity
