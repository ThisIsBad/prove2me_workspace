import Mathlib

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Theorem 9 (McDiarmid's inequality)** (p. 467). Let `X_1, …, X_n` be independent random
variables with values in `A` (the coordinates under the product `μ_1 ⊗ ⋯ ⊗ μ_n` of probability
measures, not necessarily equal), and let `f : A^n → ℝ` be measurable with
`|f(x) − f(x_1, …, x_{i−1}, x'_i, x_{i+1}, …, x_n)| ≤ c_i` for every `i`, `x` and `x'_i`. Then for every
`t > 0`, `P{f(X) − E f(X) ≥ t} ≤ exp(−2t² / Σ_i c_i²)`. -/
theorem mcdiarmid_inequality {A : Type*} [MeasurableSpace A] (n : ℕ)
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) (c : Fin n → ℝ)
    (hc : ∀ (i : Fin n) (x : Fin n → A) (a : A), |f x - f (Function.update x i a)| ≤ c i)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ f x - ∫ y, f y ∂(Measure.pi μ)} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2)) := by sorry

end RadGauss.RiskBound

