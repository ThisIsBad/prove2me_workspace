import Mathlib
import Definitions.Def_FuzzyGames_Walras_Basic

namespace FuzzyGames.Walras

/-- Proof of Theorem 4.1 (Aubin 1981, p. 6): if `x̄` belongs to the fuzzy core, then
`0 ∉ co(⋃ᵢ Q(i))`. -/
theorem zero_not_mem_convexHull_Q {n l : ℕ} (E : Economy n l) (hE : E.Assumptions)
    (xbar : Fin n → Fin l → ℝ) (hx : xbar ∈ E.fuzzyCore) :
    (0 : Fin l → ℝ) ∉ convexHull ℝ (⋃ i, E.Q xbar i) := by sorry

end FuzzyGames.Walras

