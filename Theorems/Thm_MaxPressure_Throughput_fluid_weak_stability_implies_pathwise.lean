import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

open MeasureTheory

namespace MaxPressure.Throughput

/-- Theorem 3, p. 203: weak stability of the corresponding fluid model
implies pathwise stability of the stochastic network. -/
theorem fluid_weak_stability_implies_pathwise {I J K : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (hP : P.Valid N Pr)
    (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ)
    (heq : ∀ ω, NetworkEquations N P Z T ω)
    (FM : (ℝ → Fin I → ℝ) → (ℝ → Fin J → ℝ) → Prop)
    (hcorresponding : ∀ ω Zb Tb,
      IsFluidLimit N P Z T ω Zb Tb → FM Zb Tb)
    (hweak : WeaklyStable FM) : PathwiseStable Pr Z := by sorry

end MaxPressure.Throughput

