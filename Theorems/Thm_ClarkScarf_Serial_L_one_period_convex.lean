import Mathlib
import Definitions.Def_ClarkScarf_Serial_Model

open MeasureTheory Set

namespace ClarkScarf.Serial

/-- §2, p. 478, item 2, for the lead time λ = 2: the expected discounted one-period cost
`α ∫₀^∞∫₀^∞ L(y - t₁ - t₂) φ(t₁) φ(t₂) dt₂ dt₁` is a convex function of `y`. -/
theorem L_one_period_convex (M : Model) :
    ConvexOn ℝ univ (fun y : ℝ => M.α * ∫ t₁ in Ioi (0 : ℝ), ∫ t₂ in Ioi (0 : ℝ),
      M.L (y - t₁ - t₂) * M.φ t₁ * M.φ t₂) := by sorry

end ClarkScarf.Serial

