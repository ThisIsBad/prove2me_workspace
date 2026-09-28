import Mathlib

open MeasureTheory Matrix

namespace StochLinOpt.LowerBound

/-- The decision set of the lower bound for `n = 2`: the unit circle
`D₂ = S¹ = {x ∈ ℝ² : x₁² + x₂² = 1}`. -/
def unitCircle : Set (Fin 2 → ℝ) := {x | x ⬝ᵥ x = 1}

/-- The optimal expected cost `μ · x* = min_{x ∈ D₂} μ · x` of the mean vector `μ`.
The image is nonempty and bounded (`|μ · x| ≤ ‖μ‖` on the circle), so the infimum is attained. -/
noncomputable def optCost (μ : Fin 2 → ℝ) : ℝ :=
  sInf ((fun x => μ ⬝ᵥ x) '' unitCircle)

/-- The point `μ(θ) = ½ (cos θ, sin θ)` of the circle `D₂ / 2` of radius `1/2`. With `θ` uniform
on `[0, 2π)`, `μ(θ)` is uniform on `D₂ / 2`. -/
noncomputable def meanVec (θ : ℝ) : Fin 2 → ℝ :=
  ![Real.cos θ / 2, Real.sin θ / 2]

/-- The cost value `ℓ ∈ {−1, +1}` encoded by a Boolean: `true ↦ +1`, `false ↦ −1`. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- A (possibly randomised) algorithm for the circle bandit. All internal randomness is a seed
`s : S`, drawn once from a probability measure on `S`. Before round `t + 1` (0-based index `t`)
the algorithm has observed the `t` costs `ℓ₁, …, ℓ_t ∈ {±1}` (encoded as `Fin t → Bool`) and plays
`play t s (ℓ₁, …, ℓ_t)`, a point of the unit circle, measurable in the seed. -/
structure RandomizedPolicy (S : Type*) [MeasurableSpace S] where
  /-- The decision `x_{t+1}` as a function of the seed and the observed costs `ℓ₁, …, ℓ_t`. -/
  play : (t : ℕ) → S → (Fin t → Bool) → Fin 2 → ℝ
  /-- Every decision lies on the unit circle `D₂`. -/
  play_mem : ∀ t s h, play t s h ∈ unitCircle
  /-- Every decision is a measurable function of the seed. -/
  measurable_play : ∀ t h, Measurable fun s => play t s h

/-- The decision on the 0-based round `t < T` (the paper's round `t + 1`) when the seed is `s` and
the full cost string of the horizon is `ℓ`: it depends only on `ℓ` restricted to rounds `< t`. -/
def RandomizedPolicy.decisionAt {S : Type*} [MeasurableSpace S] (π : RandomizedPolicy S)
    (T : ℕ) (s : S) (ℓ : Fin T → Bool) (t : Fin T) : Fin 2 → ℝ :=
  π.play t s (fun i => ℓ (Fin.castLE t.isLt.le i))

/-- Probability of the cost string `ℓ ∈ {±1}^T` given the mean `μ` and the seed `s`: on each round
the cost is `+1` with probability `(1 + μ · x_t)/2` and `−1` otherwise (mean `μ · x_t`),
independently of the past given the decision. -/
noncomputable def costStringProb {S : Type*} [MeasurableSpace S] (π : RandomizedPolicy S)
    (T : ℕ) (s : S) (μ : Fin 2 → ℝ) (ℓ : Fin T → Bool) : ℝ :=
  ∏ t : Fin T, (1 + signVal (ℓ t) * (μ ⬝ᵥ π.decisionAt T s ℓ t)) / 2

/-- The cumulative regret `R_T = ∑_{t=1}^T (μ · x_t − μ · x*)` along the cost string `ℓ`. -/
noncomputable def cumulativeRegret {S : Type*} [MeasurableSpace S] (π : RandomizedPolicy S)
    (T : ℕ) (s : S) (μ : Fin 2 → ℝ) (ℓ : Fin T → Bool) : ℝ :=
  ∑ t : Fin T, (μ ⬝ᵥ π.decisionAt T s ℓ t - optCost μ)

/-- `E(R_T | μ, s)`: the expected cumulative regret over the observed costs, for a fixed mean `μ`
and a fixed seed `s`. -/
noncomputable def condExpectedRegret {S : Type*} [MeasurableSpace S] (π : RandomizedPolicy S)
    (T : ℕ) (s : S) (μ : Fin 2 → ℝ) : ℝ :=
  ∑ ℓ : Fin T → Bool, costStringProb π T s μ ℓ * cumulativeRegret π T s μ ℓ

/-- The Bayesian expected regret `E R = E_μ E(R | μ)` of Theorem 3 (`n = 2`): the seed `s ∼ ρ`,
the mean `μ = μ(θ)` with `θ` uniform on `[0, 2π)` (so `μ` is uniform on `D₂ / 2`), and the costs
drawn as in `costStringProb`. -/
noncomputable def expectedRegret {S : Type*} [MeasurableSpace S] (ρ : Measure S)
    (π : RandomizedPolicy S) (T : ℕ) : ℝ :=
  ∫ s, (2 * Real.pi)⁻¹ *
    (∫ θ in Set.Ico 0 (2 * Real.pi), condExpectedRegret π T s (meanVec θ)) ∂ρ

/-- The posterior bias after one observation. If before round `t` the posterior probability of
`μ = μ₁` (against `μ = μ₂`) is `p`, and on round `t` the decision is `x` and the observed cost is
`ℓ ∈ {±1}`, then Bayes' rule (likelihood of `ℓ` under `μᵢ` is `(1 + ℓ μᵢ · x)/2`) gives
`b_{t+1} = Pr(μ = μ₁ | H_{t+1}) − Pr(μ = μ₂ | H_{t+1})`, which is this expression. -/
noncomputable def biasUpdate (μ₁ μ₂ x : Fin 2 → ℝ) (p ℓ : ℝ) : ℝ :=
  (p * (1 + ℓ * (μ₁ ⬝ᵥ x)) - (1 - p) * (1 + ℓ * (μ₂ ⬝ᵥ x))) /
    (p * (1 + ℓ * (μ₁ ⬝ᵥ x)) + (1 - p) * (1 + ℓ * (μ₂ ⬝ᵥ x)))

end StochLinOpt.LowerBound
