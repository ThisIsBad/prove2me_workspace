import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

/-- Example 2, (3.13), including the terminal identity using the forward integral. -/
theorem equation_3_13 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
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
    AntonelliBFSDE.SingularExample.L1NormDt P T (fun t ω => U t ω -
      (J₀ ω + (∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
        M s.toNNReal ω * Real.sin ((T : ℝ) - s)) +
       (∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
        Yc s.toNNReal ω * Real.cos ((T : ℝ) - s)))) = 0 ∧
    (∀ᵐ ω ∂P, UT T J₀ V ω =
      J₀ ω + (∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
        M s.toNNReal ω * Real.sin ((T : ℝ) - s)) +
      (∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
        Yc s.toNNReal ω * Real.cos ((T : ℝ) - s))) := by sorry

end AntonelliBFSDE.NonsingularExample

