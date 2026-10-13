import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `A_n := {α ∈ ℝ^d | 1+α·R_{n+1} > 0 ℙ-a.s.}` (Bäuerle–Rieder, p. 89, PDF 103), the strict
version used for logarithmic utility. -/
def ConsumptionInvestmentMarket.AfracLog (M : ConsumptionInvestmentMarket Ω d) (n : ℕ) :
    Set (Fin d → ℝ) :=
  {α | ∀ᵐ ω ∂M.measIP, 0 < 1 + ∑ k, α k * M.R (n + 1) ω k}

/-- The generic one-period logarithmic-utility sub-problem, Eq. (4.11) (Bäuerle–Rieder, p. 89,
PDF 103): `v_n := sup_{α ∈ A_n} 𝔼[log(1+α·R_{n+1})]`. -/
noncomputable def ConsumptionInvestmentMarket.vLog (M : ConsumptionInvestmentMarket Ω d)
    (n : ℕ) : ℝ :=
  ⨆ α ∈ M.AfracLog n, ∫ ω, Real.log (1 + ∑ k, α k * M.R (n + 1) ω k) ∂M.measIP

end MDPFinance.ConsumptionInvestment
