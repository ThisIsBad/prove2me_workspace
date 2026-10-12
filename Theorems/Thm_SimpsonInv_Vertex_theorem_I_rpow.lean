import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem theorem_I_rpow {m : ℕ} (k c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hk : 1 / 2 ≤ k) (hk1 : k ≤ 1)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ Set.extremePoints ℝ (dom (m := m) T S0 Sn),
      IsMinOn (costPow k c r T S0 Sn) (dom (m := m) T S0 Sn) v := by sorry

end SimpsonInv.Vertex

