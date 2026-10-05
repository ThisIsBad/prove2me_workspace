import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm96

namespace FloydAlgorithms.ShortestPath

/-- Algorithm 96, comment, pp. 344–345: the final Boolean matrix records
chains of one or more initially true parent links. -/
theorem algorithm96_eq_transGen {n : ℕ} (b : Fin n → Fin n → Bool)
    (i j : Fin n) :
    algorithm96 b i j = true ↔ Relation.TransGen (fun a c => b a c = true) i j := by sorry

end FloydAlgorithms.ShortestPath

