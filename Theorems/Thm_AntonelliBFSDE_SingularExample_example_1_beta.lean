import Mathlib
import Definitions.Def_AntonelliBFSDE_SingularExample_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

/-- Example 1, p. 791: if `β` is the constant mean of the martingale
obtained by adding (3.8) and (3.9), then `β(1-T)=E(J₀+Y)>0`. -/
theorem example_1_beta {Ω : Type*} [mΩ : MeasurableSpace Ω]
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
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      Integrable (fun ω => U r.toNNReal ω + V r.toNNReal ω) P ∧
      (∫ ω, U r.toNNReal ω + V r.toNNReal ω ∂P) =
        (∫ ω, J₀ ω + xiDt T (fun u v => u + v) Y U V 0 ω ∂P) ∧
      (∫ ω, U r.toNNReal ω + V r.toNNReal ω ∂P) =
        (∫ ω, J₀ ω ∂P) +
        (∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ ω, U s.toNNReal ω + V s.toNNReal ω ∂P) +
        (∫ ω, Y ω ∂P)) ∧
    (∫ ω, J₀ ω + xiDt T (fun u v => u + v) Y U V 0 ω ∂P) *
      (1 - (T : ℝ)) = ∫ ω, J₀ ω + Y ω ∂P ∧
    0 < ∫ ω, J₀ ω + Y ω ∂P := by sorry

end AntonelliBFSDE.SingularExample

