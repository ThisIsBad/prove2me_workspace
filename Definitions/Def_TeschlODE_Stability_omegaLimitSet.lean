import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.3, p. 193: the `ω_σ`-limit set of `x` (`σ = 1` for `ω₊`, `σ = -1` for `ω₋`):
the points `y ∈ M` for which there is a sequence of times `t_k ∈ I x` with `t_k → σ∞` and
`Φ(t_k, x) → y`. -/
def omegaLimitSet {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n))) (σ : ℝ)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | y ∈ M ∧ ∃ t : ℕ → ℝ, (∀ k, t k ∈ I x) ∧
    Filter.Tendsto (fun k => σ * t k) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => Φ (t k) x) Filter.atTop (nhds y)}

end TeschlODE.Stability
