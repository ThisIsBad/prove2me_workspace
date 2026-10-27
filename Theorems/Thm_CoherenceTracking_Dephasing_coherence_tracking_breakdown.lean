import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem coherence_tracking_breakdown (hbar γ : ℝ) (hhbar : 0 < hbar) (hγ : 0 < γ)
    (ρ0 : Qmat) (hρ0 : IsQubitState ρ0) (hc : 0 < coherence ρ0) :
    -- (i) no-go, (36)–(38): any controls, any constant-coherence solution of (32)
    (∀ (T : ℝ) (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat),
        ρ 0 = ρ0 → SolvesMaster hbar γ ω ρ T →
        (∀ t ∈ Set.Ico 0 T, coherence (ρ t) = coherence ρ0) →
        (∀ t ∈ Set.Ico 0 T,
            blochVec (ρ t) 2 ^ 2 = blochVec ρ0 2 ^ 2 - 2 * γ * coherence ρ0 * t) ∧
        T ≤ breakdownTime γ (blochVec ρ0)) ∧
    -- (ii) achievability, (37), (41)–(42): the tracked state solves (32) and keeps c on [0, t_b)
    (blochVec ρ0 2 ≠ 0 → ∀ ω0 : ℝ → ℝ,
        trackedState γ (blochVec ρ0) 0 = ρ0 ∧
        ∀ t ∈ Set.Ico 0 (breakdownTime γ (blochVec ρ0)),
          IsQubitState (trackedState γ (blochVec ρ0) t) ∧
          coherence (trackedState γ (blochVec ρ0) t) = coherence ρ0 ∧
          blochVec (trackedState γ (blochVec ρ0) t) 0 = blochVec ρ0 0 ∧
          blochVec (trackedState γ (blochVec ρ0) t) 1 = blochVec ρ0 1 ∧
          HasDerivAt (trackedState γ (blochVec ρ0))
            (masterRHS hbar γ (trackingFields γ (blochVec ρ0) ω0 t)
              (trackedState γ (blochVec ρ0) t)) t) ∧
    -- (iii) divergence of the control fields at t_b
    (blochVec ρ0 2 ≠ 0 → ∀ ω0 : ℝ → ℝ,
        Filter.Tendsto
          (fun t => trackingFields γ (blochVec ρ0) ω0 t 1 ^ 2 +
            trackingFields γ (blochVec ρ0) ω0 t 2 ^ 2)
          (nhdsWithin (breakdownTime γ (blochVec ρ0)) (Set.Iio (breakdownTime γ (blochVec ρ0))))
          Filter.atTop) := by sorry
end CoherenceTracking.Dephasing

