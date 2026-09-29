import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Theorem 1 (first claim), p. 185: along every run of method (3.3),
`∑_{i ≥ 0} r_{M_i}(x_i)³ ≤ (12/L₀)(f(x₀) − f*)`, with `r_{M_i}(x_i) = ‖x_i − x_{i+1}‖`. -/
theorem run_sum_cubes_le {n : ℕ}
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
    (fstar : ℝ) (hfstar : ∀ y ∈ F, fstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    Summable (fun i => ‖x i - x (i + 1)‖ ^ 3) ∧
      ∑' i, ‖x i - x (i + 1)‖ ^ 3 ≤ 12 / L₀ * (f x₀ - fstar) := by sorry

end CubicNewton.Nonconvex
