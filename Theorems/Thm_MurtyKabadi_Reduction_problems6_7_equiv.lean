import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem problems6_7_equiv {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ) :
    (∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0) ↔ ∃ p ∈ P n, f2 d d0 δ p.1 p.2 ≤ 0 := by sorry

end MurtyKabadi.Reduction
