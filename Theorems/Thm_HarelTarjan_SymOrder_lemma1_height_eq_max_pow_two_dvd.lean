import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym

namespace HarelTarjan.SymOrder

/-- Lemma 1 (p. 342): the height of a vertex `v` is the largest integer `h` such that `2^h`
divides `sym(v)`. -/
theorem lemma1_height_eq_max_pow_two_dvd {d : ℕ} (v : Vertex d) :
    2 ^ height v ∣ sym v ∧ ¬ 2 ^ (height v + 1) ∣ sym v := by sorry

end HarelTarjan.SymOrder
