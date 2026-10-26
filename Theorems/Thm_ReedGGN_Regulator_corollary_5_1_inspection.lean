import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation
import Definitions.Def_ReedGGN_Regulator_FluidInput

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Corollary 5.1 (p. 18): for a service law `μ` (support in `[0, ∞)`, mean `1`),
with `F_0 = F_e`, `Q̄₀ = 1` and `Ā = e`, the input of (4.7) equals `1` for `t ≥ 0`, and
`Q̄ ≡ 1` is the unique càdlàg solution of
`Q̄(t) = 1 + ∫_0^t (Q̄(t − s) − 1)^+ dF(s)` on `[0, ∞)`. -/
theorem corollary_5_1_inspection (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_nonneg : μ (Set.Iio 0) = 0) (hμ_int : Integrable id μ)
    (hμ_mean : ∫ s, s ∂μ = 1) :
    (∀ t, 0 ≤ t → fluidInput 1 (fun r => 1 - Fe μ r) μ t = 1) ∧
    SolvesRegulator μ (-1) (fluidInput 1 (fun r => 1 - Fe μ r) μ) (fun _ => 1) ∧
    (∀ Q : ℝ → ℝ, IsCadlag Q →
      SolvesRegulator μ (-1) (fluidInput 1 (fun r => 1 - Fe μ r) μ) Q →
      Set.EqOn Q (fun _ => 1) (Set.Ici 0)) := by sorry

end ReedGGN.Regulator

