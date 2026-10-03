import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market
import Definitions.Def_MDPFinance_ConsumptionInvestment_PowerAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.3.6 (Bäuerle–Rieder, p. 97, PDF 111). Under Assumption (FM) (`hFM2`), let
`Uc(x)=Up(x)=x^γ/γ`, `0<γ<1`, `δ:=(1-γ)⁻¹`. Let the positive `(d_n)` satisfy `d_N = 1/γ` and
`d_n^δ = γ^{-δ} + ((1+i_{n+1})^γ v_n)^δ d_{n+1}^δ` for `n < N` (`v_n` the value of problem
(4.7)). Then: a) `V_n(x) = d_n x^γ`, `x ≥ 0`; b) the optimal consumption is
`c_n^*(x) = x(γd_n)^{-δ}` and the optimal amounts invested in the stocks are
`a_n^*(x) = x((γd_n)^δ-1)/(γd_n)^δ · α_n^*`, `x ≥ 0`, `α_n^*` the optimal solution of (4.7), the
strategy `(f_0^*, …, f_{N-1}^*)`, `f_n^* = (c_n^*, a_n^*)`, being optimal; moreover
`d_n ≥ d_{n+1}`, so `c_n^*(x) ≤ c_{n+1}^*(x)`. -/
theorem power_utility_ci_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hFM2 : M.FM2) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdomU : M.domU = Set.Ici (0 : ℝ)) (hUc : ∀ x ≥ (0 : ℝ), M.Uc x = x ^ γ / γ)
    (hUp : ∀ x ≥ (0 : ℝ), M.Up x = x ^ γ / γ)
    (dseq : ℕ → ℝ) (hdpos : ∀ n ≤ M.N, 0 < dseq n) (hdN : dseq M.N = 1 / γ)
    (hdrec : ∀ n < M.N,
      dseq n ^ ((1 - γ)⁻¹) = γ ^ (-(1 - γ)⁻¹) +
        ((1 + M.i (n + 1)) ^ γ * M.vPower γ n) ^ ((1 - γ)⁻¹) * dseq (n + 1) ^ ((1 - γ)⁻¹)) :
    (∀ n ≤ M.N, ∀ x ≥ (0 : ℝ), M.V n x = ((dseq n * x ^ γ : ℝ) : EReal)) ∧
      (∀ n < M.N, dseq (n + 1) ≤ dseq n) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ≥ (0 : ℝ), (fstar n x).1 = x * (γ * dseq n) ^ (-(1 - γ)⁻¹)) ∧
          (∀ n < M.N, ∀ x ≥ (0 : ℝ), (fstar n x).2 =
            fun k => x * (((γ * dseq n) ^ (1 - γ)⁻¹ - 1) / (γ * dseq n) ^ (1 - γ)⁻¹) *
              αstar n k) ∧
          ∀ x ≥ (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.ConsumptionInvestment
