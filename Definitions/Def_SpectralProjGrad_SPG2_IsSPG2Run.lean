import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad
import Definitions.Def_SpectralProjGrad_Shared_nonmonotoneRef

namespace SpectralProjGrad.SPG2

/-- The nonmonotone Armijo test (3) of SPG2 at iteration `k` for the trial step `lam`:
`f(x_k + lam d_k) ≤ max_{0≤j≤min{k,M-1}} f(x_{k-j}) + γ lam ⟨d_k, g(x_k)⟩`, where
`d_k = P(x_k - α_k g(x_k)) - x_k`. -/
def SPG2Test {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (M : ℕ) (γ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) (k : ℕ) (lam : ℝ) : Prop :=
  f (x k + lam • SpectralProjGrad.Shared.scaledProjGrad P f (α k) (x k)) ≤
    SpectralProjGrad.Shared.nonmonotoneRef f x M k + γ * lam * inner ℝ (SpectralProjGrad.Shared.scaledProjGrad P f (α k) (x k)) (gradient f (x k))

/-- Step 3 of Algorithm 2.1 (the safeguarded spectral step): with `b = ⟨s, y⟩`, return `α_max`
if `b ≤ 0`, and otherwise `min {α_max, max {α_min, ⟨s, s⟩ / b}}`. -/
noncomputable def spectralStep {n : ℕ} (αmin αmax : ℝ) (s y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if inner ℝ s y ≤ 0 then αmax else min αmax (max αmin (inner ℝ s s / inner ℝ s y))

/-- `(x, α)` is an infinite run of Algorithm SPG2 (Algorithm 2.1 with the backtracking Step 2 of
Algorithm 2.2) on `Ω`, for the objective `f` with gradient `g = ∇f`, the projection `P`, and the
parameters `M, α_min, α_max, γ, σ₁, σ₂`; iterations are indexed from `0`.

* `x₀ ∈ Ω` and `α₀ ∈ [α_min, α_max]`.
* Step 1 never stops: `‖P(x_k - g(x_k)) - x_k‖ ≠ 0` for every `k`.
* Step 2: at every iteration `k` there is a finite backtracking trace `μ_0 = 1, μ_1, …, μ_m` with
  `μ_{i+1} ∈ [σ₁ μ_i, σ₂ μ_i]` (rule (2)), test (3) fails at `μ_0, …, μ_{m-1}` and holds at `μ_m`,
  and `x_{k+1} = x_k + μ_m d_k` with `d_k = P(x_k - α_k g(x_k)) - x_k`.
* Step 3: `α_{k+1}` is the safeguarded spectral step for `s_k = x_{k+1} - x_k` and
  `y_k = g(x_{k+1}) - g(x_k)`. -/
structure IsSPG2Run {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : ℕ) (αmin αmax γ σ₁ σ₂ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) : Prop where
  start_mem : x 0 ∈ Ω
  start_step : α 0 ∈ Set.Icc αmin αmax
  step1_not_stop : ∀ k, ‖P (x k - gradient f (x k)) - x k‖ ≠ 0
  step2_backtrack : ∀ k, ∃ (m : ℕ) (μ : ℕ → ℝ),
    μ 0 = 1 ∧
    (∀ i < m, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) ∧
    (∀ i < m, ¬ SPG2Test f P M γ x α k (μ i)) ∧
    SPG2Test f P M γ x α k (μ m) ∧
    x (k + 1) = x k + μ m • SpectralProjGrad.Shared.scaledProjGrad P f (α k) (x k)
  step3_spectral : ∀ k,
    α (k + 1) = spectralStep αmin αmax (x (k + 1) - x k) (gradient f (x (k + 1)) - gradient f (x k))

end SpectralProjGrad.SPG2
