import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Lemma 4, (2.12), p. 183: if `M ≥ L` then `T_M(x) ∈ F` and
`f(T_M(x)) ≤ f̄_M(x)`. Stated, as its proof via Lemma 2 requires, for `x ∈ int F` with
`f(x) ≤ f(x₀)`. -/
theorem step_mem_and_accept {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (M : ℝ) (hLM : L ≤ M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior F)
    (hfx : f x ≤ f x₀) (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    T ∈ F ∧ f T ≤ f x + CubicNewton.Shared.cubicModel g H M x T := by sorry

end CubicNewton.Nonconvex
