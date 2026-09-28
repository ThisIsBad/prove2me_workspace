import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.StarConvex

/-- Nesterov–Polyak 2006, Lemma 4, inequality (2.10), p. 183: under the standing assumptions of
Section 2, for any `x ∈ F` and any positive parameter `M`, let `T = T_M(x)` be a global minimizer
of the cubic model (2.4), so that `f̄_M(x) = f(x) + cubicModel g H M x T`. Then for every `y ∈ F`,
`f̄_M(x) ≤ f(y) + ((L + M)/6)‖y − x‖³`, i.e. `f̄_M(x) ≤ min_{y ∈ F} [f(y) + ((L + M)/6)‖y − x‖³]`. -/
theorem model_value_le {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L M : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ∀ y ∈ F, f x + CubicNewton.Shared.cubicModel g H M x T ≤ f y + (L + M) / 6 * ‖y - x‖ ^ 3 := by sorry

end CubicNewton.StarConvex

