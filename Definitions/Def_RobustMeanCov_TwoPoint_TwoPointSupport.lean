import Mathlib

namespace RobustMeanCov.TwoPoint

/-- The family `𝒬` (Popescu 2007, pp. 100–101): coefficient triples `(A, B, C)` of quadratics
`q(y) = A y² + B y + C` with `q(y) ≤ u(y)` for every real `y`. -/
def SupportFamily (u : ℝ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  {ABC | ∀ y : ℝ, ABC.1 * y ^ 2 + ABC.2.1 * y + ABC.2.2 ≤ u y}

/-- A probability law on the real line with support `{a, b}`, mean `μ` and variance `σ²` exists:
there is a mass `p ∈ (0, 1)` on `a` (and `1 - p` on `b`) giving mean `μ` and variance `σ²`. -/
def TwoPointLawExists (a b μ σ : ℝ) : Prop :=
  ∃ p ∈ Set.Ioo (0 : ℝ) 1,
    p * a + (1 - p) * b = μ ∧ p * (a - μ) ^ 2 + (1 - p) * (b - μ) ^ 2 = σ ^ 2

/-- Definition 1 (Popescu 2007, p. 101), with respect to `(μ, σ²)`: some quadratic
`q(y) = A y² + B y + C` supports `u` from below and meets it at two points `a < b`, and a law
with mean `μ`, variance `σ²` and support `{a, b}` exists. -/
def TwoPointSupportWrt (u : ℝ → ℝ) (μ σ : ℝ) : Prop :=
  ∃ a b A B C : ℝ, a < b ∧ (A, B, C) ∈ SupportFamily u ∧
    A * a ^ 2 + B * a + C = u a ∧ A * b ^ 2 + B * b + C = u b ∧
    TwoPointLawExists a b μ σ

/-- Definition 1: `u` satisfies the two-point support property if it satisfies it with respect to
every `(μ, σ²)` with `σ > 0`. -/
def TwoPointSupport (u : ℝ → ℝ) : Prop :=
  ∀ μ σ : ℝ, 0 < σ → TwoPointSupportWrt u μ σ

end RobustMeanCov.TwoPoint
