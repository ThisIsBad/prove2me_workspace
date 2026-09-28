import Mathlib

open MeasureTheory

namespace DistInterpRO.Consistency

/-- The box `𝒵ᵢ = {xᵢ + δ | ‖δ‖∞ ≤ ε}` around a sample point `xᵢ` (Xu–Caramanis–Mannor 2012,
p. 98). On `Fin m → ℝ` the norm is the sup norm `‖·‖∞`, so this is the closed sup-norm ball
of radius `ε` centred at `xᵢ`. -/
def box {m : ℕ} (xi : Fin m → ℝ) (ε : ℝ) : Set (Fin m → ℝ) :=
  Metric.closedBall xi ε

/-- The distribution set `𝒫ₙ` of Eq. (6) (p. 98): the Borel probability measures `μ` on `ℝᵐ`
such that `μ(⋃_{i ∈ S} 𝒵ᵢ) ≥ |S|/n` for every `S ⊆ [1 : n]` (indices are `Fin n`). -/
def distSet {m n : ℕ} (Z : Fin n → Set (Fin m → ℝ)) : Set (Measure (Fin m → ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧
    ∀ S : Finset (Fin n), ENNReal.ofReal ((S.card : ℝ) / n) ≤ μ (⋃ i ∈ S, Z i)}

/-- The uniform box kernel `K(z) = 𝟏(‖z‖∞ ≤ 1) / 2ᵐ` (p. 98). -/
noncomputable def kernel {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  if ‖z‖ ≤ 1 then 1 / (2 : ℝ) ^ m else 0

/-- The kernel density estimator
`hₙ(x) = (n ε^m)⁻¹ ∑_{i=1}^n K((x − xᵢ)/ε)` built from the sample `x₁, …, xₙ` (here
`xs : Fin n → ℝᵐ`) with bandwidth `ε` (p. 98, with the printed `/ϵ` read as `/ϵ(n)`, as on
p. 99). For `n = 0` it is the zero function. -/
noncomputable def kde {m n : ℕ} (ε : ℝ) (xs : Fin n → Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  ((n : ℝ) * ε ^ m)⁻¹ * ∑ i : Fin n, kernel (ε⁻¹ • (x - xs i))

/-- The box-robust sample objective of Theorem 3.1 (p. 98):
`(1/n) ∑_{i=1}^n inf_{‖δᵢ‖∞ ≤ ε} f(v, xᵢ + δᵢ)`.
Each infimum is over the nonempty index set `{δ | ‖δ‖∞ ≤ ε}` when `ε ≥ 0`. -/
noncomputable def roObjective {V : Type*} {m n : ℕ} (f : V → (Fin m → ℝ) → ℝ) (ε : ℝ)
    (xs : Fin n → Fin m → ℝ) (v : V) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, ⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (xs i + δ.1)

/-- The equicontinuity modulus of Theorem 3.1 (ii) (p. 98):
`d(ε) = sup_{v, x, ‖δ‖∞ ≤ ε} |f(v, x) − f(v, x + δ)|` (the printed `max` read as `sup`). -/
noncomputable def modulus {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  ⨆ v : V, ⨆ x : Fin m → ℝ, ⨆ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, |f v x - f v (x + δ.1)|

end DistInterpRO.Consistency
