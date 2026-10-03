import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `C_n := 𝔼[R_n R_n^⊤]` (Bäuerle–Rieder, Eq. (4.34), p. 121, PDF 135). -/
noncomputable def MVMarket.Cmat (M : MVMarket Ω d) (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => ∫ ω, M.R n ω j * M.R n ω k ∂M.measIP

/-- `𝔼[R_n] ∈ ℝ^d`. -/
noncomputable def MVMarket.Evec (M : MVMarket Ω d) (n : ℕ) : Fin d → ℝ :=
  fun j => ∫ ω, M.R n ω j ∂M.measIP

/-- `ℓ_n := 𝔼[R_n]^⊤ C_n^{-1} 𝔼[R_n]` (Bäuerle–Rieder, Eq. (4.34), p. 121, PDF 135). -/
noncomputable def MVMarket.ell (M : MVMarket Ω d) (n : ℕ) : ℝ :=
  dotProduct (M.Evec n) ((M.Cmat n)⁻¹.mulVec (M.Evec n))

end MDPFinance.MeanVariance
