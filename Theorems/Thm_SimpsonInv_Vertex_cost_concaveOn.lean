import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem cost_concaveOn {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 ≤ r i) :
    ConcaveOn ℝ (dom (m := m) T S0 Sn) (cost c r T S0 Sn) := by sorry

end SimpsonInv.Vertex

