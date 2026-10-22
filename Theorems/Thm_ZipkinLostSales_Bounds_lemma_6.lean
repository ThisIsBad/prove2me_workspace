import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

namespace ZipkinLostSales.Bounds

/-- Lemma 6, p. 940: the policy `z̄_T(v)` is in `Z(s̄)`. With one period to go (`k = 0`,
`t = T`), for every `v ∈ ZipkinLostSales.LNatural.V` the smallest minimizer of `g_T(v, ·) = q(v, ·)` over `z ≥ 0` exists and
satisfies the bounds of `Z(s̄)` at `v`. -/
theorem lemma_6 {L : ℕ} (M : Data) (hM : Assumptions L M) (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) :
    ∃ z : ℝ, IsOptOrder M 0 v z ∧ InZ L M v z := by sorry

end ZipkinLostSales.Bounds

