import Mathlib
import Definitions.Def_SelfDualLP_Complexity_Neighborhood

open Matrix

namespace SelfDualLP.Complexity

/-- Proof of Theorem 6, second bullet (p. 62), the Mizuno–Todd–Ye corrector estimate. Let
`n̂ ≥ 1` and let `x̂, ŝ, d̂_x, d̂_s ∈ ℝ^{n̂}` satisfy (14) with `γ = 1`: `x̂ > 0`, `ŝ > 0`,
`X̂d̂_s + Ŝd̂_x = −(X̂ŝ − μ̂e)`, `d̂_xᵀd̂_s = 0`, with `μ̂ = x̂ᵀŝ/n̂`. If
`‖X̂ŝ − μ̂e‖ ≤ (1/2)μ̂` then `x̂(1) = x̂ + d̂_x > 0`, `ŝ(1) = ŝ + d̂_s > 0`,
`‖X̂(1)ŝ(1) − μ̂(1)e‖ ≤ (1/4)μ̂(1)` and `μ̂(1) = μ̂`. -/
theorem mty_corrector_bullet {N : ℕ} (hN : 1 ≤ N) (x s dx ds : Fin N → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (hnewton : ∀ j, x j * ds j + s j * dx j = -(x j * s j - 1 * muHat x s))
    (horth : dx ⬝ᵥ ds = 0)
    (hcent : deviationHat x s ≤ (1 / 2) * muHat x s) :
    (∀ j, 0 < (x + dx) j) ∧ (∀ j, 0 < (s + ds) j) ∧
    deviationHat (x + dx) (s + ds) ≤ (1 / 4) * muHat (x + dx) (s + ds) ∧
    muHat (x + dx) (s + ds) = muHat x s := by sorry

end SelfDualLP.Complexity

