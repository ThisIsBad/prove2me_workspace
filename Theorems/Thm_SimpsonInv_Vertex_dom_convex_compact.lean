import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem dom_convex_compact {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) :
    Convex ℝ (dom (m := m) T S0 Sn) ∧ IsCompact (dom (m := m) T S0 Sn) := by sorry

end SimpsonInv.Vertex

