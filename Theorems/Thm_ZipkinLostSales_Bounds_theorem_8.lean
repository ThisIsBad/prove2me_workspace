import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- Theorem 8, p. 940: for all `t ≤ T` (every `k`, `t = T − k`), `f_t(v)` is nondecreasing in `v`
on `V`, and the smallest optimal orders `z̄_t(v)` and `z̄_T(v)` exist and satisfy
`z̄_t(v) ≤ z̄_T(v)`. -/
theorem theorem_8 {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ) :
    MonotoneOn (fB M (k + 1)) (ZipkinLostSales.LNatural.V L) ∧
      ∀ v ∈ ZipkinLostSales.LNatural.V L,
        ∃ z z' : ℝ, IsOptOrder M k v z ∧ IsOptOrder M 0 v z' ∧ z ≤ z' := by sorry

end ZipkinLostSales.Bounds

