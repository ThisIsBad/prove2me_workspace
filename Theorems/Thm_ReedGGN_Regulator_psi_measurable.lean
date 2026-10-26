import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, Measurability (pp. 34–35): for each `t ≥ 0`, the map
`u ↦ Ψ^a_B(u)(t)` is measurable from `D[0,∞)` with its Kolmogorov (cylinder) σ-algebra to
`ℝ`. Together with `psi_cadlag` this is the measurability of `Ψ^a_B : D[0,∞) → D[0,∞)`. -/
theorem psi_measurable (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    ∀ t, 0 ≤ t → Measurable (fun u : Dpath => psi μ a u.path t) := by sorry

end ReedGGN.Regulator

