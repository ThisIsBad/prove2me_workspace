import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_MDPFinance_MeanVariance_MRcdSeq

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Proposition 4.7.2 (Bäuerle–Rieder, p. 129, PDF 143), the binomial-model value of `P(λ)`
(`p > q`, under the section's standing assumptions). With `γ_1 := 1-((1-p)/(1-q))^N`,
`γ_2 := p^N((1-q)^N-(1-p)^N)/((p(1-q))^N - (q(1-p))^N)`,
`λ^* := min(q^N/(p^N-q^N), ((1-p)^N(1-γ)^{-1}-(1-q)^N)/((1-q)^N-(1-p)^N))`: a) the value of `P(λ)`
is `(μ-x_0)λ - x_0` if `λ ∈ [0,λ^*]` and `γ ≥ γ_1`, else `-∞`; b) the optimal policies `π^*` for
`P(λ)` are stationary, `π^* = (f^b,…,f^b)` with `f^b(x) = max((x+b)/(1-u), (x+b)/(1-d))`, where
`b = -x_0` if `λ ∈ [0,λ^*)`, `b ∈ [-x_0,∞)` if `λ = λ^*` and `γ ≥ γ_2`, `b ∈ (-∞,-x_0]` if
`λ = λ^*` and `γ_1 ≤ γ ≤ γ_2` (each such `b` giving an optimal policy, in the finite-value case
`γ ≥ γ_1`). -/
theorem plambda_binomial_value {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.q < M.p) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = 1 - ((1 - M.p) / (1 - M.q)) ^ M.N)
    (hγ2 : γ2 = M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N))
    (hlamstar : lamstar = min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ((lam ∈ Set.Icc (0 : ℝ) lamstar ∧ M.γ ≥ γ1 →
        (⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) =
          (((M.μ - M.x0) * lam - M.x0 : ℝ) : EReal)) ∧
      (¬ (lam ∈ Set.Icc (0 : ℝ) lamstar ∧ M.γ ≥ γ1) →
        (⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) = ⊥)) ∧
      (M.γ ≥ γ1 →
        (lam < lamstar →
          M.IsOptimalPLambda lam (fun _ x => max ((x + -M.x0) / (1 - M.u)) ((x + -M.x0) / (1 - M.d)))) ∧
        (lam = lamstar → M.γ ≥ γ2 → ∀ b, -M.x0 ≤ b →
          M.IsOptimalPLambda lam (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d)))) ∧
        (lam = lamstar → γ1 ≤ M.γ → M.γ ≤ γ2 → ∀ b, b ≤ -M.x0 →
          M.IsOptimalPLambda lam (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d))))) := by sorry

end MDPFinance.MeanVariance
