import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

theorem gamma_maps_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V) :
    L1NormD P IA IC (Fop IA J f U V) < ⊤ ∧
    (∀ t ≤ T, Integrable (xiG IC g Y U V t) P) ∧
    ∀ W : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P IC g Y U V W → L1NormD P IA IC W < ⊤ := by sorry

end AntonelliBFSDE.BackwardForward

