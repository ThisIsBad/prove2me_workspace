import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact

/-- Proof of Theorem 3.5, pp. 362–363: if ȳ is an optimal solution to (D_r), r > 0, and
x̄ ∈ X minimizes L_r(·, ȳ) over X, then ∇_y L_r(x̄, ȳ) = 0 and ȳ maximizes L_r(x̄, ·) over ℝ^m. -/
theorem stationary_at_dual_optimal {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : PenaltyLag.Asymptotic.Mult m) (hybar : IsDualOptimal X f₀ f r ybar)
    (xbar : E) (hxbar : xbar ∈ X) (hmin : ∀ x ∈ X, PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar ≤ PenaltyLag.Asymptotic.Lr f₀ f r x ybar) :
    HasGradientAt (fun y => PenaltyLag.Asymptotic.Lr f₀ f r xbar y) 0 ybar ∧ ∀ y, PenaltyLag.Asymptotic.Lr f₀ f r xbar y ≤ PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar := by sorry

end PenaltyLag.Exact

