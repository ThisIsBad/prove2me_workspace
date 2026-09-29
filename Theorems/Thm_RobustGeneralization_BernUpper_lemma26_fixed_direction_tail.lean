import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 32, Lemma 26. For one sample `p = (x, y)` of the
`(θ⋆, τ)`-Bernoulli model with `θ⋆ = pm θ`, `z = xy = zvec p`, and any fixed unit vector `w`
(Euclidean norm `1`) with `⟨w, 2τθ⋆⟩ ≥ 0`, `P[⟨w, z⟩ ≤ 0] ≤ exp(−2τ²⟨w, θ⋆⟩²)`. -/
theorem lemma26_fixed_direction_tail {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) (w : E d) (hw : ‖w‖ = 1)
    (hwθ : 0 ≤ inner ℝ w ((2 * τ) • pm θ)) :
    bprob θ τ (fun p => inner ℝ w (zvec p) ≤ 0)
      ≤ Real.exp (-(2 * τ ^ 2 * (inner ℝ w (pm θ)) ^ 2)) := by sorry

end RobustGeneralization.BernUpper
