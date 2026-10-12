import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem exists_isMinOn {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ dom (m := m) T S0 Sn, IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v := by sorry

end SimpsonInv.Vertex

