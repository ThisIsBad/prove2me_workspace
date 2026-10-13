import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

/-- The two displayed representations in Example 1, p. 790, read as
`dt ⊗ P`-almost-everywhere identities. -/
theorem example_1_formulas {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (hT : 0 < T)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYint : Integrable Y P)
    (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + |v|)
      (fun u v => u + v) Y U V) :
    L1NormDt P T (fun t ω => U t ω -
      Real.exp (t : ℝ) * (J₀ ω +
        ∫ s in Set.Ioc (0 : ℝ) (t : ℝ),
          Real.exp (-s) * |V s.toNNReal ω|)) = 0 ∧
    (∀ t ≤ T, Integrable
      (fun ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
        ∫ s in Set.Ioc (t : ℝ) (T : ℝ),
          Real.exp (s - (t : ℝ)) * U s.toNNReal ω) P) ∧
    ∃ W : ℝ≥0 → Ω → ℝ,
      AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T
        (fun t ω => Real.exp ((T : ℝ) - (t : ℝ)) * Y ω +
          ∫ s in Set.Ioc (t : ℝ) (T : ℝ),
            Real.exp (s - (t : ℝ)) * U s.toNNReal ω) W ∧
      L1NormDt P T (fun t ω => W t ω - V t ω) = 0 := by sorry

end AntonelliBFSDE.SingularExample

