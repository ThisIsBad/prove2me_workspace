import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 31, Lemma 25. For one sample `p = (x, y)` of the
`(θ⋆, τ)`-Bernoulli model with `θ⋆ = pm θ`, `z = xy` and the unit vector `ŵ = z / ‖z‖₂ = unitZ p`,
`P[⟨ŵ, θ⋆⟩ ≤ τ√d] ≤ exp(−τ²d/2)`. -/
theorem lemma25_unit_inner_theta_tail {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) :
    bprob θ τ (fun p => inner ℝ (unitZ p) (pm θ) ≤ τ * Real.sqrt d)
      ≤ Real.exp (-(τ ^ 2 * d / 2)) := by sorry

end RobustGeneralization.BernUpper
