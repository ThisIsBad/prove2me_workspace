import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic

namespace PenaltyLag.Exact

/-- Corollary 3.4, p. 362 (r > 0 against r = 0): L_r and L₀ have the same Kuhn–Tucker
vectors and the same saddle points, and (x̄, ȳ) is a saddle point of L_r iff the ordinary
Kuhn–Tucker conditions hold. -/
theorem corollary_3_4 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) :
    (IsKTVector X f₀ f r ybar ↔ IsKTVector0 X f₀ f ybar) ∧
    (IsSaddle X f₀ f r xbar ybar ↔ IsSaddle0 X f₀ f xbar ybar) ∧
    (IsSaddle X f₀ f r xbar ybar ↔ KuhnTuckerConditions X f₀ f xbar ybar) := by sorry

end PenaltyLag.Exact

