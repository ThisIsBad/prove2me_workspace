import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem theorem1_lower_bound (h k : ℕ) {N : Type*} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hrep : Function.Injective rep)
    (hk : AnswersLeafQueriesIn ptr rep k) :
    Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ h)) - 2 < (k : ℝ) := by sorry

end HarelTarjan.PointerLB

