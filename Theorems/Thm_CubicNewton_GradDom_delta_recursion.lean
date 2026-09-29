import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
import Definitions.Def_CubicNewton_GradDom_IsGradDominated2
import Definitions.Def_CubicNewton_GradDom_omegaTilde

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Section 4.2, Eq. (4.17), p. 195 (proof of Theorem 7): for a gradient
dominated `f` of degree 2 and every run of method (3.3), with `ω̃ = L₀⁴ / (324 (L + L₀)⁶ τ_f³)` and
`δ_k = (f(x_k) − f(x*))/ω̃`, one has `δ_k ≥ δ_{k+1} + δ_{k+1}^{3/4}` for every `k ≥ 0`. -/
theorem delta_recursion {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (τ : ℝ) (xs : EuclideanSpace ℝ (Fin n)) (hdom : IsGradDominated2 F f g τ xs)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    ∀ k : ℕ, (f (x k) - f xs) / omegaTilde L₀ L τ ≥
      (f (x (k + 1)) - f xs) / omegaTilde L₀ L τ +
        ((f (x (k + 1)) - f xs) / omegaTilde L₀ L τ) ^ (3 / 4 : ℝ) := by sorry

end CubicNewton.GradDom

