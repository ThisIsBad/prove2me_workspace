import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `c_n := (λ + (1-γ)⁻¹)((1-p)/(1-q))^{N-n}` (Bäuerle–Rieder, p. 126, PDF 140). -/
noncomputable def MeanRiskMarket.cSeq (M : MeanRiskMarket Ω) (lam : ℝ) (n : ℕ) : ℝ :=
  (lam + (1 - M.γ)⁻¹) * ((1 - M.p) / (1 - M.q)) ^ (M.N - n)

/-- `d_n := λ(p/q)^{N-n}` (Bäuerle–Rieder, p. 126, PDF 140). -/
noncomputable def MeanRiskMarket.dSeq (M : MeanRiskMarket Ω) (lam : ℝ) (n : ℕ) : ℝ :=
  lam * (M.p / M.q) ^ (M.N - n)

end MDPFinance.MeanVariance
