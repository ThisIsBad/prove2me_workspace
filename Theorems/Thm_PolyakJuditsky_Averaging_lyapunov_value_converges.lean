import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_PolyakJuditsky_Averaging_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- Proof of Theorem 2, Part 1 (p. 849): under Assumptions 3.1–3.4, with `Δ_t = x_t - x*` the
error of the iterate of Eq. (7), `V(Δ_t)` converges almost surely to a finite limit.
`R` is assumed continuous (the paper states no regularity of `R`; its proof needs
`⟪∇V(x - x*), R x⟫` bounded away from `0` on every annulus `ε ≤ |x - x*| ≤ ρ`, p. 849–850,
which continuity and Assumption 3.1 give). -/
theorem lyapunov_value_converges {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (x₀ xstar : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ ξ0 : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (V : EuclideanSpace ℝ (Fin N) → ℝ)
    (G S : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ)
    (hR : Continuous R) (h31 : LyapunovAssumption R xstar V)
    (h32 : LinearizationAssumption R xstar G lam)
    (h33 : NoiseAssumption P ℱ x₀ γ R ξ ξ0 xstar S) (h34 : StepAssumption γ lam) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, Tendsto (fun t => V (saIterate x₀ γ R ξ t ω - xstar)) atTop (𝓝 c) := by sorry

end PolyakJuditsky.Averaging
