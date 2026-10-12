import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem theorem_II {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (S : Fin (m + 1) → ℝ) (j : Fin (m + 1))
    (hj : S j = extVec S0 Sn S j.val + T (j.val + 1)) :
    cost c r T S0 Sn S =
      cost c (coupledR r (j.val + 1)) (coupledT T (j.val + 1)) S0 Sn (Fin.removeNth j S) := by sorry

end SimpsonInv.Vertex

