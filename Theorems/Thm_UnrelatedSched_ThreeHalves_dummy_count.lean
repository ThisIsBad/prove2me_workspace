import Mathlib
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, proof of Theorem 5, p. 7: when every
`a_j` lies in at least one triple (`t_j ≥ 1`), the total number `Σ_j (t_j − 1)` of dummy jobs is
`m − n`, stated without subtraction as `Σ_j (t_j − 1) + n = m`. -/
theorem dummy_count {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : ∀ j : Fin n, 1 ≤ typeCount T j) :
    (∑ j : Fin n, (typeCount T j - 1)) + n = m := by sorry

end UnrelatedSched.ThreeHalves

