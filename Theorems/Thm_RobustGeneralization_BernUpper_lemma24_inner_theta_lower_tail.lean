import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

/-- Schmidt et al., arXiv:1804.11285v2, p. 31, Lemma 24. For one sample `p = (x, y)` of the
`(θ⋆, τ)`-Bernoulli model with `θ⋆ = pm θ` and `z = xy = zvec p`, and every `δ > 0`,
`P[⟨z, θ⋆⟩ ≤ 2τd − √(2d log 1/δ)] ≤ δ`. The hypothesis `1 ≤ d` is added: at `d = 0` the event
is `0 ≤ 0` and has probability `1`. -/
theorem lemma24_inner_theta_lower_tail {d : ℕ} (hd : 1 ≤ d) (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) (δ : ℝ) (hδ : 0 < δ) :
    bprob θ τ (fun p => inner ℝ (zvec p) (pm θ)
        ≤ 2 * τ * d - Real.sqrt (2 * d * Real.log (1 / δ))) ≤ δ := by sorry

end RobustGeneralization.BernUpper
