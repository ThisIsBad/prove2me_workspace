import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem lemma_I {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (hm : 1 ≤ m)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i) :
    ∀ v ∈ interior (dom (m := m) T S0 Sn),
      ¬ IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v := by sorry

end SimpsonInv.Vertex

