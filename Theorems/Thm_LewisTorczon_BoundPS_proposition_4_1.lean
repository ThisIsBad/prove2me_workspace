import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 4.1**, p. 8. Let `g = ∇f`. If `f` is differentiable at every point of the closed
segment `[x, x + d]` with `g` continuous on it, `g(x) ≠ 0`, `g(x)ᵀd ≤ -ε‖d‖`, and
`‖d‖ < ω(x, ε/2)` — encoded as: some `δ > ‖d‖` has `‖g(y) - g(x)‖ < ε/2` whenever `‖y - x‖ < δ` —
then `f(x + d) - f(x) ≤ -(ε/2)‖d‖`. -/
theorem proposition_4_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (ε δ : ℝ) (hε : 0 < ε)
    (hdiff : ∀ y ∈ segment ℝ x (x + d), DifferentiableAt ℝ f y)
    (hcont : ContinuousOn (gradient f) (segment ℝ x (x + d)))
    (hgx : gradient f x ≠ 0) (hdesc : inner ℝ (gradient f x) d ≤ -ε * ‖d‖)
    (hω : ∀ y, ‖y - x‖ < δ → ‖gradient f y - gradient f x‖ < ε / 2) (hd : ‖d‖ < δ) :
    f (x + d) - f x ≤ -(ε / 2) * ‖d‖ := by sorry

end LewisTorczon.BoundPS
