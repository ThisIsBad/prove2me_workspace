import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial

namespace QueueingFundamentals.AdvMarkov

/-- Eq. (3.55), p.161: for a steady-state solution of the `M/M/1` retrial queue with
`ρ = λ/μ < 1`, the partial generating functions are, for `z ∈ [−1, 1]`,
`P_0(z) = (1 − ρz)((1 − ρ)/(1 − ρz))^{(λ/γ)+1}` and `P_1(z) = ρ((1 − ρ)/(1 − ρz))^{(λ/γ)+1}`. -/
theorem retrial_pgf_closed_form (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (ρ : ℝ) (hρ : ρ = lam / mu) (hρ1 : ρ < 1)
    (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      pgf p0 z = (1 - ρ * z) * ((1 - ρ) / (1 - ρ * z)) ^ (lam / gam + 1) ∧
      pgf p1 z = ρ * ((1 - ρ) / (1 - ρ * z)) ^ (lam / gam + 1) := by sorry

end QueueingFundamentals.AdvMarkov

