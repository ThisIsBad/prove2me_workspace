import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

/-- Example 2, pp. 791–792: nonexistence at the nonsingular critical horizon. -/
theorem example_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P) (hT : (T : ℝ) = Real.pi / 2)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hYbounded : ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C) :
    ¬ ∃ U V : ℝ≥0 → Ω → ℝ,
      AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v) (fun u _ => u) Y U V := by sorry

end AntonelliBFSDE.NonsingularExample

