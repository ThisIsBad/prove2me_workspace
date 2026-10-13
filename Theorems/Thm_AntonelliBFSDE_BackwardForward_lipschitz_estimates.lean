import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

theorem lipschitz_estimates {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V U' V' : ℝ≥0 → Ω → ℝ) (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V)
    (hU' : MemL1D P IA IC U') (hV' : MemL1D P IA IC V') :
    (∀ ω, ∀ t ≤ T, ENNReal.ofReal |Fop IA J f U V t ω - Fop IA J f U' V' t ω| ≤
        ENNReal.ofReal k * pathDist IA IC U V U' V' 0 t ω) ∧
    ∀ W W' : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P IC g Y U V W → IsGVersion 𝓕 P IC g Y U' V' W' →
      ∀ t ≤ T, Integrable (fun ω => (pathDist IA IC U V U' V' t T ω).toReal) P ∧
        ∀ᵐ ω ∂P, |W t ω - W' t ω| ≤
          k * (P[fun ω => (pathDist IA IC U V U' V' t T ω).toReal | 𝓕 t]) ω := by sorry

end AntonelliBFSDE.BackwardForward

