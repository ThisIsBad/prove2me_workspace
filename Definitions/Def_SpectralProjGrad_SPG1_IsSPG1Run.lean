import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_nonmonotoneRef

namespace SpectralProjGrad.SPG1

/-- The nonmonotone Armijo test (1) of SPG1 at iteration `k` for the trial step `lam`, along the
projection arc: with the trial point `x₊ = P(x_k - lam g(x_k))`,
`f(x₊) ≤ max_{0≤j≤min{k,M-1}} f(x_{k-j}) + γ ⟨x₊ - x_k, g(x_k)⟩`
(no factor `lam` in the last term). -/
def SPG1Test {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (M : ℕ) (γ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) (lam : ℝ) : Prop :=
  f (P (x k - lam • gradient f (x k))) ≤
    SpectralProjGrad.Shared.nonmonotoneRef f x M k + γ * inner ℝ (P (x k - lam • gradient f (x k)) - x k) (gradient f (x k))

/-- Step 3 of Algorithm 2.1 (the safeguarded spectral step): with `b = ⟨s, y⟩`, return `α_max`
if `b ≤ 0`, and otherwise `min {α_max, max {α_min, ⟨s, s⟩ / b}}`. -/
noncomputable def spectralStep {n : ℕ} (αmin αmax : ℝ) (s y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if inner ℝ s y ≤ 0 then αmax else min αmax (max αmin (inner ℝ s s / inner ℝ s y))

/-- `(x, α)` is an infinite run of Algorithm SPG1 (Algorithm 2.1) on `Ω`, for the objective `f`
with gradient `g = ∇f`, the projection `P`, and the parameters `M, α_min, α_max, γ, σ₁, σ₂`;
iterations are indexed from `0`.

* `x₀ ∈ Ω` and `α₀ ∈ [α_min, α_max]`.
* Step 1 never stops: `‖P(x_k - g(x_k)) - x_k‖ ≠ 0` for every `k`.
* Step 2: at every iteration `k` there is a finite backtracking trace `μ_0 = α_k, μ_1, …, μ_m`
  with `μ_{i+1} ∈ [σ₁ μ_i, σ₂ μ_i]` (rule (2)), test (1) fails at `μ_0, …, μ_{m-1}` and holds at
  `μ_m`, and `x_{k+1} = P(x_k - μ_m g(x_k))`.
* Step 3: `α_{k+1}` is the safeguarded spectral step for `s_k = x_{k+1} - x_k` and
  `y_k = g(x_{k+1}) - g(x_k)`. -/
structure IsSPG1Run {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : ℕ) (αmin αmax γ σ₁ σ₂ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) : Prop where
  start_mem : x 0 ∈ Ω
  start_step : α 0 ∈ Set.Icc αmin αmax
  step1_not_stop : ∀ k, ‖P (x k - gradient f (x k)) - x k‖ ≠ 0
  step2_backtrack : ∀ k, ∃ (m : ℕ) (μ : ℕ → ℝ),
    μ 0 = α k ∧
    (∀ i < m, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) ∧
    (∀ i < m, ¬ SPG1Test f P M γ x k (μ i)) ∧
    SPG1Test f P M γ x k (μ m) ∧
    x (k + 1) = P (x k - μ m • gradient f (x k))
  step3_spectral : ∀ k,
    α (k + 1) = spectralStep αmin αmax (x (k + 1) - x k) (gradient f (x (k + 1)) - gradient f (x k))

end SpectralProjGrad.SPG1
