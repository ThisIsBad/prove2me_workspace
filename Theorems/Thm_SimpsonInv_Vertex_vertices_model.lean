import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem vertices_model {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i) :
    Set.extremePoints ℝ (dom (m := m) T 0 0) =
        {S : Fin m → ℝ | ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1)} ∩
          dom (m := m) T 0 0 ∧
      (Set.extremePoints ℝ (dom (m := m) T 0 0)).ncard = 2 ^ m := by sorry

end SimpsonInv.Vertex

