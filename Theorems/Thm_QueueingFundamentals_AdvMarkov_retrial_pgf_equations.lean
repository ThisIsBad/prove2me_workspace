import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial

namespace QueueingFundamentals.AdvMarkov

/-- Eqs. (3.50)–(3.52), p.160: for a steady-state solution of the `M/M/1` retrial queue, the
partial generating functions `P_0`, `P_1` satisfy, for `z ∈ (−1, 1)`,
`λP_0(z) + zγP_0'(z) = μP_1(z)` (3.50), `(λ + μ)P_1(z) = λP_0(z) + γP_0'(z) + λzP_1(z)` (3.51)
and `P_0'(z) = λρ/(γ(1 − ρz)) · P_0(z)` (3.52), with `ρ = λ/μ < 1`. -/
theorem retrial_pgf_equations (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (ρ : ℝ) (hρ : ρ = lam / mu) (hρ1 : ρ < 1)
    (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    ∀ z ∈ Set.Ioo (-1 : ℝ) 1,
      DifferentiableAt ℝ (pgf p0) z ∧
      lam * pgf p0 z + z * gam * deriv (pgf p0) z = mu * pgf p1 z ∧
      (lam + mu) * pgf p1 z = lam * pgf p0 z + gam * deriv (pgf p0) z + lam * z * pgf p1 z ∧
      deriv (pgf p0) z = lam * ρ / (gam * (1 - ρ * z)) * pgf p0 z := by sorry

end QueueingFundamentals.AdvMarkov

