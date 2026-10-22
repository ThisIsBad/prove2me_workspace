import Mathlib
import Definitions.Def_SelfDualLP_Complexity_Neighborhood

open Matrix

namespace SelfDualLP.Complexity

/-- Proof of Theorem 6, first bullet (p. 62), the Mizuno–Todd–Ye predictor estimate. Let
`n̂ ≥ 1` and let `x̂, ŝ, d̂_x, d̂_s ∈ ℝ^{n̂}` satisfy (14) with `γ = 0`: `x̂ > 0`, `ŝ > 0`,
`X̂d̂_s + Ŝd̂_x = −X̂ŝ`, `d̂_xᵀd̂_s = 0`. Write `μ̂ = x̂ᵀŝ/n̂`, `x̂(α) = x̂ + αd̂_x`,
`ŝ(α) = ŝ + αd̂_s`, `μ̂(α) = x̂(α)ᵀŝ(α)/n̂`. If `‖X̂ŝ − μ̂e‖ ≤ (1/4)μ̂` then for every
`α ∈ [0, 8^{−1/4}/√n̂]`: `x̂(α) > 0`, `ŝ(α) > 0`, `‖X̂(α)ŝ(α) − μ̂(α)e‖ ≤ (1/2)μ̂(α)` and
`μ̂(α) = (1 − α)μ̂`. -/
theorem mty_predictor_bullet {N : ℕ} (hN : 1 ≤ N) (x s dx ds : Fin N → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (hnewton : ∀ j, x j * ds j + s j * dx j = -(x j * s j - 0 * muHat x s))
    (horth : dx ⬝ᵥ ds = 0)
    (hcent : deviationHat x s ≤ (1 / 4) * muHat x s) :
    ∀ α : ℝ, 0 ≤ α → α ≤ (8 : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt N →
      (∀ j, 0 < (x + α • dx) j) ∧ (∀ j, 0 < (s + α • ds) j) ∧
      deviationHat (x + α • dx) (s + α • ds) ≤ (1 / 2) * muHat (x + α • dx) (s + α • ds) ∧
      muHat (x + α • dx) (s + α • ds) = (1 - α) * muHat x s := by sorry

end SelfDualLP.Complexity

