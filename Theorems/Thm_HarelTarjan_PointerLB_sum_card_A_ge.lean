import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem sum_card_A_ge {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k) :
    (h : ℕ∞) * 2 ^ h ≤ 2 * ∑ x ∈ leaves h, (A ptr rep k x).encard := by sorry

end HarelTarjan.PointerLB

