import Mathlib
import Definitions.Def_Avram2004_Exit_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

/-- (2), p. 216: whenever the moment generating function of `X_t` exists at `θ`,
`𝔼[e^{θX_t}] = e^{tψ(θ)}` with `ψ(θ) = log 𝔼[e^{θX_1}]`. -/
theorem mgf_eq_exp_psi {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (t : ℝ≥0) (θ : ℝ) (hint : Integrable (fun ω => Real.exp (θ * X t ω)) P) :
    ∫ ω, Real.exp (θ * X t ω) ∂P = Real.exp ((t : ℝ) * Shared.psi P X θ) := by sorry

end Avram2004.Exit
