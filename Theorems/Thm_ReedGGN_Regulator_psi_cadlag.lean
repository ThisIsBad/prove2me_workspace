import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, Measurability (p. 34): `Ψ^a_B` maps `D[0,∞)` into `D[0,∞)`:
for every càdlàg `u`, `t ↦ ∫_0^t (u(t − s) + a)^+ dB(s)` is càdlàg. -/
theorem psi_cadlag (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) (u : ℝ → ℝ)
    (hu : IsCadlag u) : IsCadlag (psi μ a u) := by sorry

end ReedGGN.Regulator

