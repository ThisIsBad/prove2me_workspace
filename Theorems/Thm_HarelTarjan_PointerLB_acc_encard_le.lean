import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

namespace HarelTarjan.PointerLB

theorem acc_encard_le {N : Type*} (ptr : N → Fin 2 → Option N) (a : N) (j : ℕ) :
    (acc ptr j a).encard + 1 ≤ 2 ^ (j + 1) := by sorry

end HarelTarjan.PointerLB

