import Mathlib
import Definitions.Def_LogRegretOCO_OGD_Model

namespace LogRegretOCO.OGD

/-- **Eq. (1)** (p. 175): for an `H`-strongly convex `f` on a convex set `P` and `x, y ∈ P`,
`2 (f x − f y) ≤ 2 ∇f(x)ᵀ(x − y) − H ‖y − x‖²`. -/
theorem strong_convexity_lower_bound {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (H : ℝ)
    (f : E n → ℝ) (hf : IsHStrongConvex P H f) (x y : E n) (hx : x ∈ P) (hy : y ∈ P) :
    2 * (f x - f y) ≤ 2 * inner ℝ (gradient f x) (x - y) - H * ‖y - x‖ ^ 2 := by sorry

end LogRegretOCO.OGD

