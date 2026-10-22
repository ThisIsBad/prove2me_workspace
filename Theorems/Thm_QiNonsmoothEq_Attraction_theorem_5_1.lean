import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Attraction_Setting
open Filter Topology NonsmoothNewton.Local

namespace QiNonsmoothEq.Attraction

/-- Qi 1993, Theorem 5.1, p. 238 (attraction theorem): for a locally Lipschitz, B-differentiable
`F : ℝⁿ → ℝⁿ` and a descent direction method `x^{k+1} = x^k + α_k d^k` with
`‖F(x^{k+1})‖ ≤ ‖F(x^k)‖` (5.1), if a limiting point `x*` of `{x^k}` is a BD-regular zero of `F`
and, near `x*`, `α_k ≤ s` and `‖d^k‖ ≤ p ‖F(x^k)‖` (5.2), then `x^k → x*`. -/
theorem theorem_5_1 {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (hB : ∀ y, QiNonsmoothEq.Local.BDiffAt F y)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hstep : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 ≤ α k)
    (hdesc : ∀ k, ‖F (x (k + 1))‖ ≤ ‖F (x k)‖)
    (xstar : EuclideanSpace ℝ (Fin n)) (hclu : MapClusterPt xstar atTop x)
    (hzero : F xstar = 0) (hreg : BDRegularAt F xstar)
    (δ₁ s p : ℝ) (hδ₁ : 0 < δ₁) (hs : 0 < s) (hp : 0 < p)
    (hloc : ∀ k, ‖x k - xstar‖ ≤ δ₁ → α k ≤ s ∧ ‖d k‖ ≤ p * ‖F (x k)‖) :
    Tendsto x atTop (𝓝 xstar) := by sorry

end QiNonsmoothEq.Attraction

