import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_RegimeMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

variable {EY : Type*} [Fintype EY] [MeasurableSpace EY] {d : ℕ}

/-- `A(j) := {α ∈ ℝ^d | 1+α·R(j) ≥ 0 Q_j-a.e.}`, the admissible fractions in regime `j`
(Bäuerle–Rieder, p. 104, PDF 118). -/
def RegimeSwitchingMarket.Afrac (M : RegimeSwitchingMarket EY d) (j : EY) : Set (Fin d → ℝ) :=
  {α | ∀ᵐ z ∂(M.Q j), 0 ≤ 1 + ∑ k, α k * z k}

/-- The generic one-period power-utility sub-problem, Eq. (4.20) (Bäuerle–Rieder, p. 104, PDF
118): `v(j) := sup_{α ∈ A(j)} 𝔼[(1+α·R(j))^γ]`. -/
noncomputable def RegimeSwitchingMarket.vPower (M : RegimeSwitchingMarket EY d) (γ : ℝ)
    (j : EY) : ℝ :=
  ⨆ α ∈ M.Afrac j, ∫ z, (1 + ∑ k, α k * z k) ^ γ ∂(M.Q j)

end MDPFinance.ConsumptionInvestment
