import Mathlib
import Definitions.Def_FuzzyGames_Walras_Basic

namespace FuzzyGames.Walras

/-- Proof of Theorem 4.1 (Aubin 1981, p. 6): every Walras equilibrium belongs to the fuzzy
core. -/
theorem walras_subset_fuzzyCore {n l : ℕ} (E : Economy n l) (hE : E.Assumptions) :
    E.walras ⊆ E.fuzzyCore := by sorry

end FuzzyGames.Walras

