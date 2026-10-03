import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.1, p. 231, (8.8): the stable (`σ = 1`) or unstable (`σ = -1`) set of `Λ`,
`W^σ(Λ) = {x ∈ M | lim_{t→σ∞} d(Φ_t(x), Λ) = 0}`. For the local flow the limit requires the
solution through `x` to exist for all `σ t ≥ 0`, i.e. `x` is `σ` complete; the limit
`t → σ∞` is written as `s → ∞` with `t = σ s`. Here `d(x, Λ)` is `Metric.infDist x Λ`. -/
def stableSet {E : Type*} [NormedAddCommGroup E] (M : Set E) (I : E → Set ℝ)
    (Φ : ℝ → E → E) (σ : ℝ) (Λ : Set E) : Set E :=
  {x | x ∈ M ∧ (∀ t : ℝ, 0 ≤ σ * t → t ∈ I x) ∧
    Filter.Tendsto (fun s : ℝ => Metric.infDist (Φ (σ * s) x) Λ) Filter.atTop (nhds 0)}

end TeschlODE.HigherDim
