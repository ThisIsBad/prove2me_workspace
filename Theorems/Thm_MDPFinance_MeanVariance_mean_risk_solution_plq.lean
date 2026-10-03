import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.7.4 (Bäuerle–Rieder, p. 131, PDF 145), `p < q` case, under the section's standing
assumptions. With `γ_1 := (q^N-p^N)/q^N`, `γ_2 := (1-p)^N(q^N-p^N)/(((1-p)q)^N-((1-q)p)^N)`,
`λ^* := min((1-q)^N/((1-p)^N-(1-q)^N), (p^N(1-γ)^{-1}-q^N)/(q^N-p^N))`: a) the value of `(MR)`
is the same formula as in Theorem 4.7.3, with these `λ^*`, `γ_1`; b) the optimal policy `π^*` is
stationary, `π^* = (f^*,…,f^*)`, with `f^*(x) = (1/(1-d))((μ-x_0)q^N/(p^N-q^N) - x_0 + x)` if
`γ_1 ≤ γ ≤ γ_2`, and `f^*(x) = (1/(1-u))((x_0-μ)(1-q)^N/((1-q)^N-(1-p)^N) - x_0 + x)` if
`γ ≥ γ_2`. -/
theorem mean_risk_solution_plq {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.p < M.q) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = (M.q ^ M.N - M.p ^ M.N) / M.q ^ M.N)
    (hγ2 : γ2 = (1 - M.p) ^ M.N * (M.q ^ M.N - M.p ^ M.N) /
      (((1 - M.p) * M.q) ^ M.N - ((1 - M.q) * M.p) ^ M.N))
    (hlamstar : lamstar = min ((1 - M.q) ^ M.N / ((1 - M.p) ^ M.N - (1 - M.q) ^ M.N))
      ((M.p ^ M.N * (1 - M.γ)⁻¹ - M.q ^ M.N) / (M.q ^ M.N - M.p ^ M.N))) :
    (M.γ ≥ γ1 → M.VMR = (((M.μ - M.x0) * lamstar - M.x0 : ℝ) : EReal)) ∧
      (¬ M.γ ≥ γ1 → M.VMR = ⊥) ∧
      (γ1 ≤ M.γ → M.γ ≤ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.d)⁻¹ * ((M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) - M.x0 + x))) ∧
      (M.γ ≥ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.u)⁻¹ * ((M.x0 - M.μ) * ((1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) -
          M.x0 + x))) := by sorry

end MDPFinance.MeanVariance
