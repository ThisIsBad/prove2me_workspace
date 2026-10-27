import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem bloch_equations (hbar γ : ℝ) (hhbar : 0 < hbar) :
    (∀ (ω : Fin 3 → ℝ) (ρ : Qmat),
        blochVec (masterRHS hbar γ ω ρ) = (blochMatrix γ ω).mulVec (blochVec ρ)) ∧
    (∀ (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat) (T : ℝ),
        SolvesMaster hbar γ ω ρ T → SolvesBloch γ ω (fun t => blochVec (ρ t)) T) ∧
    (∀ (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ),
        SolvesBloch γ ω v T → SolvesMaster hbar γ ω (fun t => blochState (v t)) T) := by sorry
end CoherenceTracking.Dephasing

