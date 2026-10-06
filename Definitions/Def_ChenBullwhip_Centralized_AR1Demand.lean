import Mathlib

open MeasureTheory ProbabilityTheory

namespace ChenBullwhip.Centralized

/-- Chen–Drezner–Ryan–Simchi-Levi (2000), p. 437, Eq. (1): the steady-state AR(1) demand
`D t = μ + ρ D (t - 1) + ε t` on the integer time line, with `μ ≥ 0`, `|ρ| < 1` and errors
`ε t` i.i.d. from a symmetric distribution with mean `0` and variance `σ²`.

Added relative to the page (disclosed): `σ > 0` (the paper divides by `Var(D)`), the errors and
demands are square integrable (the paper takes their variances), and the demand is in steady state:
every `D t` is square integrable and has the law of `D 0` (the paper's "it can easily be shown that
`E(D_t) = μ/(1-ρ)` and `Var(D_t) = σ²/(1-ρ²)`" presupposes the stationary solution of (1)). -/
structure AR1Demand {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] where
  /-- The constant `μ` of Eq. (1). -/
  mu : ℝ
  /-- The correlation parameter `ρ`. -/
  rho : ℝ
  /-- The error standard deviation `σ`. -/
  sigma : ℝ
  mu_nonneg : 0 ≤ mu
  abs_rho_lt_one : |rho| < 1
  sigma_pos : 0 < sigma
  /-- The error terms `ε t`. -/
  eps : ℤ → Ω → ℝ
  /-- The customer demands `D t` seen by the retailer. -/
  D : ℤ → Ω → ℝ
  measurable_D : ∀ t, Measurable (D t)
  /-- The errors are mutually independent ... -/
  eps_iIndep : iIndepFun eps P
  /-- ... and identically distributed. -/
  eps_identDistrib : ∀ t, IdentDistrib (eps t) (eps 0) P P
  /-- The error distribution is symmetric: `ε t` and `-ε t` have the same law. -/
  eps_symm : ∀ t, IdentDistrib (eps t) (fun ω => -eps t ω) P P
  eps_memLp : ∀ t, MemLp (eps t) 2 P
  eps_mean : ∀ t, ∫ ω, eps t ω ∂P = 0
  eps_variance : ∀ t, variance (eps t) P = sigma ^ 2
  /-- Eq. (1), for every outcome. -/
  recursion : ∀ t : ℤ, ∀ ω, D t ω = mu + rho * D (t - 1) ω + eps t ω
  /-- Steady state: the demands are square integrable ... -/
  D_memLp : ∀ t, MemLp (D t) 2 P
  /-- ... and all have the same law. -/
  stationary : ∀ t, IdentDistrib (D t) (D 0) P P

end ChenBullwhip.Centralized
