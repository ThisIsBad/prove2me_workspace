import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

theorem contraction {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V U' V' : ℝ≥0 → Ω → ℝ)
    (hUp : IsProgressive 𝓕 U) (hVp : IsProgressive 𝓕 V)
    (hU'p : IsProgressive 𝓕 U') (hV'p : IsProgressive 𝓕 V')
    (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V)
    (hU' : MemL1D P IA IC U') (hV' : MemL1D P IA IC V')
    (W W' : ℝ≥0 → Ω → ℝ) (hW : IsGVersion 𝓕 P IC g Y U V W)
    (hW' : IsGVersion 𝓕 P IC g Y U' V' W') :
    L1NormD P IA IC (Fop IA J f U V - Fop IA J f U' V') + L1NormD P IA IC (W - W') ≤
      ENNReal.ofReal k * HInfNorm P IA IC *
        (L1NormD P IA IC (U - U') + L1NormD P IA IC (V - V')) := by sorry

end AntonelliBFSDE.BackwardForward

