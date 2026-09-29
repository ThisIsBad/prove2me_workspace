import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Lemma 7, inequality (4.10), p. 193: at each step of method (3.3),
`f(x_k) − f(x_{k+1}) ≥ L₀ ‖f′(x_{k+1})‖^{3/2} / (3√2 (L + L₀)^{3/2})` for every `k ≥ 0`. -/
theorem run_decrease {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    ∀ k : ℕ, f (x k) - f (x (k + 1)) ≥
      L₀ * ‖g (x (k + 1))‖ ^ (3 / 2 : ℝ) / (3 * Real.sqrt 2 * (L + L₀) ^ (3 / 2 : ℝ)) := by sorry

end CubicNewton.GradDom

