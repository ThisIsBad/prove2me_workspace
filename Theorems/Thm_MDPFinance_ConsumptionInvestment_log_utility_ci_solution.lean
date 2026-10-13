import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market
import Definitions.Def_MDPFinance_ConsumptionInvestment_LogAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.3.7 (Bäuerle–Rieder, p. 99, PDF 113). Under Assumption (FM) (`hFM2`), let
`Uc(x)=Up(x)=log x`, `x > 0`. Then: a) the value functions are `V_n(x) = (N-n+1)\log x + d_n`,
`x > 0`, for some constants `d_n ∈ ℝ`; b) the optimal consumption is `c_n^*(x) = x/(N-n+1)` and
the optimal amounts invested in the stocks are `a_n^*(x) = x(N-n)/(N-n+1) · α_n^*`, `x > 0`,
`α_n^*` the optimal solution of (4.11); the strategy `(f_0^*, …, f_{N-1}^*)` is optimal. -/
theorem log_utility_ci_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hFM2 : M.FM2) (hdomU : M.domU = Set.Ioi (0 : ℝ))
    (hUc : ∀ x > (0 : ℝ), M.Uc x = Real.log x) (hUp : ∀ x > (0 : ℝ), M.Up x = Real.log x) :
    (∃ dseq : ℕ → ℝ, ∀ n ≤ M.N, ∀ x > (0 : ℝ),
        M.V n x = ((((M.N : ℝ) - n + 1) * Real.log x + dseq n : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.AfracLog n ∧
          ∫ ω, Real.log (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ∂M.measIP = M.vLog n) ∧
        ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), (fstar n x).1 = x / ((M.N : ℝ) - n + 1)) ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), (fstar n x).2 =
            fun k => x * (((M.N : ℝ) - n) / ((M.N : ℝ) - n + 1)) * αstar n k) ∧
          ∀ x > (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.ConsumptionInvestment

