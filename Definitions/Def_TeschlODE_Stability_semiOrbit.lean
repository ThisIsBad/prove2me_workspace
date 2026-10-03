import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.3, p. 192, (6.16): the forward (`σ = 1`) or backward (`σ = -1`) orbit
`γ_σ(x) = Φ((0, T_σ(x)), x)`, i.e. the points `Φ t x` with `t ∈ I x` and `σ t > 0`. -/
def semiOrbit {n : ℕ} (σ : ℝ) (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ t ∈ I x, 0 < σ * t ∧ Φ t x = y}

end TeschlODE.Stability
