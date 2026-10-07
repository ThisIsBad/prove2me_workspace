import Mathlib
import Definitions.Def_MechanismDesign_Screening_ExtremePoints

namespace MechanismDesign.Screening

/-- **Proposition 2.4 (Extreme Point Theorem)**, p.16 (Ok 2007, p.658). Let `X` be a nonempty,
compact, convex subset of a real normed vector space `E`, and let `f` be a linear function that is
continuous on `X`. Then the set of extreme points of `X` (Definition 2.4) is nonempty, and some
extreme point `e` satisfies `f(e) ≥ f(x)` for all `x ∈ X`. -/
theorem extreme_point_theorem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hne : X.Nonempty) (hcomp : IsCompact X) (hconv : Convex ℝ X)
    (f : E →ₗ[ℝ] ℝ) (hf : ContinuousOn f X) :
    {e | IsExtremePoint X e}.Nonempty ∧ ∃ e, IsExtremePoint X e ∧ ∀ x ∈ X, f x ≤ f e := by sorry

end MechanismDesign.Screening

