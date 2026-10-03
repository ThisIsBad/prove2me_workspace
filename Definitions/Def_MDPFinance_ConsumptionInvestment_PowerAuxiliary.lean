import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `A_n := {α ∈ ℝ^d | 1+α·R_{n+1} ≥ 0 ℙ-a.s.}` (Bäuerle–Rieder, p. 83/97, PDF 97/111, reused
across the pure-investment (chunk `04a`) and consumption-investment problems). -/
def ConsumptionInvestmentMarket.Afrac (M : ConsumptionInvestmentMarket Ω d) (n : ℕ) :
    Set (Fin d → ℝ) :=
  {α | ∀ᵐ ω ∂M.measIP, 0 ≤ 1 + ∑ k, α k * M.R (n + 1) ω k}

/-- The generic one-period power-utility sub-problem, Eq. (4.7) (Bäuerle–Rieder, p. 83, PDF 97):
`v_n := sup_{α ∈ A_n} 𝔼[(1+α·R_{n+1})^γ]`. -/
noncomputable def ConsumptionInvestmentMarket.vPower (M : ConsumptionInvestmentMarket Ω d)
    (γ : ℝ) (n : ℕ) : ℝ :=
  ⨆ α ∈ M.Afrac n, ∫ ω, (1 + ∑ k, α k * M.R (n + 1) ω k) ^ γ ∂M.measIP

end MDPFinance.ConsumptionInvestment
