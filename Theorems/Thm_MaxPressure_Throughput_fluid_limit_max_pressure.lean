import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

namespace MaxPressure.Throughput

/-- Lemma 4, p. 213: every fluid limit of the maximum-pressure process
satisfies fluid equation (20). -/
theorem fluid_limit_max_pressure {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : MPProcess N E Z Ta ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hlim : IsFluidLimit N P Z (activityTime E Ta) ω Zb Tb) :
    MPFluidEq N Zb Tb := by sorry

end MaxPressure.Throughput

