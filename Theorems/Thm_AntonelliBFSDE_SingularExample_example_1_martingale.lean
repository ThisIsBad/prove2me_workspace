import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

/-- Example 1, p. 791: adding (3.8) and (3.9) gives a martingale.
Equality with `U + V` is in `L¹(dt ⊗ P)`; the martingale law is for
every `s ≤ t ≤ T` up to `P`-almost-sure equality. -/
theorem example_1_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (hT : 0 < T)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYint : Integrable Y P)
    (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hsol : IsDtSystemSolution 𝓕 P T J₀ (fun u v => u + v)
      (fun u v => u + v) Y U V) :
    ∃ N : ℝ≥0 → Ω → ℝ,
      Measurable (Function.uncurry N) ∧
      (∀ t ≤ T, Integrable (N t) P ∧ StronglyMeasurable[𝓕 t] (N t) ∧
        N t =ᵐ[P] (fun ω => J₀ ω + P[xiDt T (fun u v => u + v) Y U V 0 | 𝓕 t] ω)) ∧
      (∀ s ≤ T, ∀ t ≤ T, s ≤ t → N s =ᵐ[P] P[N t | 𝓕 s]) ∧
      L1NormDt P T (fun t ω => U t ω + V t ω - N t ω) = 0 := by sorry

end AntonelliBFSDE.SingularExample

