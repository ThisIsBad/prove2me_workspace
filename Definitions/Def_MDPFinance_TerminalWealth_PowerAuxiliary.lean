import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The set of admissible fractions `A_n := {α ∈ ℝ^d | 1 + α·R_{n+1} ≥ 0  ℙ-a.s.}`
(Bäuerle–Rieder, p. 83, PDF 97), used in the power-, HARA- and log-utility one-period
sub-problems. -/
def TerminalWealthMarket.Afrac (M : TerminalWealthMarket Ω d) (n : ℕ) : Set (Fin d → ℝ) :=
  {α | ∀ᵐ ω ∂M.measIP, 0 ≤ 1 + ∑ k, α k * M.R (n + 1) ω k}

/-- The generic one-period power-utility sub-problem, Eq. (4.7) (Bäuerle–Rieder, p. 83, PDF 97):
`v_n := sup_{α ∈ A_n} 𝔼[(1+α·R_{n+1})^γ]`. -/
noncomputable def TerminalWealthMarket.vPower (M : TerminalWealthMarket Ω d) (γ : ℝ) (n : ℕ) :
    ℝ :=
  ⨆ α ∈ M.Afrac n, ∫ ω, (1 + ∑ k, α k * M.R (n + 1) ω k) ^ γ ∂M.measIP

end MDPFinance.TerminalWealth
