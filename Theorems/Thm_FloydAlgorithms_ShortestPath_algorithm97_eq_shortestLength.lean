import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Network
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm97

namespace FloydAlgorithms.ShortestPath

/-- Algorithm 97, comment, third and fourth sentences, p. 345. The
no-negative-cycle condition repairs the paper's unstated necessary premise. -/
theorem algorithm97_eq_shortestLength {n : ℕ} (w : LengthMatrix n)
    (hcycle : NoNegativeCycle w) (i j : Fin n) :
    algorithm97 w i j = shortestLength w i j := by sorry

end FloydAlgorithms.ShortestPath

