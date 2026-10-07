import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic

namespace TalagrandConc.SKModel

/-- Talagrand (12.6), p. 193. -/
theorem lipschitz (N : ℕ) (β : ℝ) (h h' : Interaction N → ℝ)
    (hN : 0 < N) (hβ : 0 < β) :
    |freeEnergy N β h - freeEnergy N β h'| ≤
      β / Real.sqrt N * ∑ p : Interaction N, |h p - h' p| := by sorry

end TalagrandConc.SKModel

