import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

/-- Example 2, p. 792: the sine-cosine form of the backward component. -/
theorem closed_form_V {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V M Yc : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P) (hT : 0 < T)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hYbounded : ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v) (fun u _ => u) Y U V)
    (hM : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => UT T J₀ V) M)
    (hYc : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => Y) Yc) :
    AntonelliBFSDE.SingularExample.L1NormDt P T (fun t ω => V t ω -
      (M t ω * Real.sin ((T : ℝ) - (t : ℝ)) +
       Yc t ω * Real.cos ((T : ℝ) - (t : ℝ)))) = 0 := by sorry

end AntonelliBFSDE.NonsingularExample

