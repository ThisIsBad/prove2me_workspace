import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

namespace ChinesePostman.Polyhedron

theorem odd_set_cut_sum_odd {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (z : E → ℤ)
    (hz : ∀ n, incidentSum G z n ≡ bParity G n [ZMOD 2])
    (S : Finset V) (hS : IsOddSet G S) :
    cutSum G z S ≡ 1 [ZMOD 2] := by sorry

end ChinesePostman.Polyhedron

