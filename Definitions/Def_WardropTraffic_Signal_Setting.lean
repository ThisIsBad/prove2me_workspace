import Mathlib

namespace WardropTraffic.Signal

/-- Appendix IV, p. 358: the average delay `T = (λx² + μy²)/(x + y − 1)` in terms of the
effective-red fractions `x = (r₁ + a₁)/c`, `y = (r₂ + a₂)/c`. -/
noncomputable def delayT (lam mu x y : ℝ) : ℝ :=
  (lam * x ^ 2 + mu * y ^ 2) / (x + y - 1)

/-- Appendix IV, p. 358: the admissible `(x, y)`: `x ≤ ξ`, `y ≤ η` (no indefinite accumulation on
either phase) and `x + y > 1` (a positive cycle `c = A/(x + y − 1)`). -/
def feasibleXY (xi eta : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ≤ xi ∧ z.2 ≤ eta ∧ 1 < z.1 + z.2}

/-- The left side of the corner condition, p. 359: `(μ/λ)η² + 2ξ(1 − η) − ξ²`. -/
noncomputable def cornerD (lam mu xi eta : ℝ) : ℝ :=
  (mu / lam) * eta ^ 2 + 2 * xi * (1 - eta) - xi ^ 2

/-- The root on the edge `y = η`, p. 359: `1 − η + √((1 − η)² + (μ/λ)η²)`. -/
noncomputable def edgeRoot (lam mu eta : ℝ) : ℝ :=
  1 - eta + Real.sqrt ((1 - eta) ^ 2 + (mu / lam) * eta ^ 2)

/-- `ξ = 1 − q₁/p₁`, p. 358. -/
noncomputable def xiOf (q₁ p₁ : ℝ) : ℝ := 1 - q₁ / p₁

/-- `η = 1 − q₂/p₂` (the page prints `1 − q₁/p₁`, a slip), p. 358. -/
noncomputable def etaOf (q₂ p₂ : ℝ) : ℝ := 1 - q₂ / p₂

/-- `λ = Aq₁/(2Qξ)`, p. 358. -/
noncomputable def lamOf (A Q q₁ p₁ : ℝ) : ℝ := A * q₁ / (2 * Q * xiOf q₁ p₁)

/-- `μ = Aq₂/(2Qη)`, p. 358. -/
noncomputable def muOf (A Q q₂ p₂ : ℝ) : ℝ := A * q₂ / (2 * Q * etaOf q₂ p₂)

/-- Equation (16), p. 339: the average delay for the intersection as a whole,
`T = (1/2Qc){q₁(r₁ + a₁)²/(1 − q₁/p₁) + q₂(r₂ + a₂)²/(1 − q₂/p₂)}`. -/
noncomputable def avgDelay16 (Q c q₁ q₂ p₁ p₂ r₁ r₂ a₁ a₂ : ℝ) : ℝ :=
  1 / (2 * Q * c) * (q₁ * (r₁ + a₁) ^ 2 / (1 - q₁ / p₁) + q₂ * (r₂ + a₂) ^ 2 / (1 - q₂ / p₂))

end WardropTraffic.Signal
