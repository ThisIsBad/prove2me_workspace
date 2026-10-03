import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.7.3 (Bäuerle–Rieder, p. 130, PDF 144), `p > q` case, under the section's standing
assumptions. With `γ_1, γ_2, λ^*` as in `plambda_binomial_value`: a) the value of `(MR)` is
`V_{MR}(x_0) = (μ-x_0)λ^*-x_0` if `γ ≥ γ_1`, else `-∞`; b) (for `γ ≥ γ_1`) the optimal policy
`π^*` is stationary, `π^* = (f^*,…,f^*)`, with `f^*(x) = (1/(1-d))((μ-x_0)q^N/(p^N-q^N) - x_0 + x)`
if `γ ≥ γ_2`, and `f^*(x) = (1/(1-u))((x_0-μ)(1-q)^N/((1-q)^N-(1-p)^N) - x_0 + x)` if
`γ_1 ≤ γ ≤ γ_2`. -/
theorem mean_risk_solution {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.q < M.p) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = 1 - ((1 - M.p) / (1 - M.q)) ^ M.N)
    (hγ2 : γ2 = M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N))
    (hlamstar : lamstar = min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N))) :
    (M.γ ≥ γ1 → M.VMR = (((M.μ - M.x0) * lamstar - M.x0 : ℝ) : EReal)) ∧
      (¬ M.γ ≥ γ1 → M.VMR = ⊥) ∧
      (M.γ ≥ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.d)⁻¹ * ((M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) - M.x0 + x))) ∧
      (γ1 ≤ M.γ → M.γ ≤ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.u)⁻¹ * ((M.x0 - M.μ) * ((1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) -
          M.x0 + x))) := by sorry

end MDPFinance.MeanVariance
