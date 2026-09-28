import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem half_leaves_occurrences {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k)
    (w : Vertex h) (i : ℕ) (hi : 1 ≤ i) (hwi : w.1.length + i = h) :
    (2 ^ (i - 1) : ℕ∞) ≤
      {x : Vertex h | IsLeaf x ∧ IsAncestor w x ∧ w ∈ A ptr rep k x}.encard := by sorry

end HarelTarjan.PointerLB

