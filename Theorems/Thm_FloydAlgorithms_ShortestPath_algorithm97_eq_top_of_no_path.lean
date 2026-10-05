import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Network
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm97

namespace FloydAlgorithms.ShortestPath

/-- Algorithm 97, comment, fourth sentence, p. 345: no path leaves the
final entry at infinity. No sign condition is needed here. -/
theorem algorithm97_eq_top_of_no_path {n : ℕ} (w : LengthMatrix n)
    (i j : Fin n)
    (h : ¬ ∃ (L : ℕ) (p : Fin (L + 1) → Fin n),
      IsPath i j L p ∧ pathLength w p ≠ ⊤) :
    algorithm97 w i j = ⊤ := by sorry

end FloydAlgorithms.ShortestPath

