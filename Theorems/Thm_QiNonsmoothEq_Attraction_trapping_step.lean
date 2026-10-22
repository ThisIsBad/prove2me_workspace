import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Attraction_Setting
open Filter Topology NonsmoothNewton.Local

namespace QiNonsmoothEq.Attraction

/-- Qi 1993, proof of Theorem 5.1, p. 239: with `c` as in (5.3), there is `δ ∈ (0, δ₁)` such
that for every `ε ∈ (0, δ)` the set
`N(x*, ε) = {x : ‖x - x*‖ ≤ ε, ‖F(x)‖ ≤ ε / (2c + sp)}` is invariant under one step of the
descent direction method: `x^k ∈ N(x*, ε)` implies `x^{k+1} ∈ N(x*, ε)`. -/
theorem trapping_step {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (xstar : EuclideanSpace ℝ (Fin n)) (hBx : QiNonsmoothEq.Local.BDiffAt F xstar) (hzero : F xstar = 0)
    (c : ℝ) (hc : ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F xstar h‖)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 ≤ α k)
    (hdesc : ∀ k, ‖F (x (k + 1))‖ ≤ ‖F (x k)‖)
    (δ₁ s p : ℝ) (hδ₁ : 0 < δ₁) (hs : 0 < s) (hp : 0 < p)
    (hloc : ∀ k, ‖x k - xstar‖ ≤ δ₁ → α k ≤ s ∧ ‖d k‖ ≤ p * ‖F (x k)‖) :
    ∃ δ : ℝ, 0 < δ ∧ δ < δ₁ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ k : ℕ,
      (‖x k - xstar‖ ≤ ε ∧ ‖F (x k)‖ ≤ ε / (2 * c + s * p)) →
      (‖x (k + 1) - xstar‖ ≤ ε ∧ ‖F (x (k + 1))‖ ≤ ε / (2 * c + s * p)) := by sorry

end QiNonsmoothEq.Attraction

