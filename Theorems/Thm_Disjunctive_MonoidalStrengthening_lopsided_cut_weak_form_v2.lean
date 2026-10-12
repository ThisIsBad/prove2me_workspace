import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic


namespace Disjunctive.MonoidalStrengthening

/-- Corollary 11.25 (Balas, *Disjunctive Programming*, Springer 2018, §11.9, p. 183). For the
normalized disjunction (11.38) `∨_i (Σ_j a_ij x_j ≥ a_i0)` with `a_i0 > 0` and background lower
bounds `Σ_j a_ij x_j ≥ b_i` satisfying the standing assumption `b_i ≤ a_i0`, for each `k ∈ Q` the
cut `δ^k x ≥ 1` is valid for every `x ≥ 0`, integer on `J₁`, satisfying the bounds and the
disjunction, where `δ^k_j := min{(a_kj + a_k0 - b_k)/a_k0, β_j}` for `j ∈ J₁` and `δ^k_j := β_j`
otherwise (`β_j = max_i a_ij/a_i0`).

Correction w.r.t. the retired version: the standing assumption `b_i ≤ a_i0` is now hypothesis
`hb`. -/
theorem lopsided_cut_weak_form_v2 {q n : ℕ} [Nonempty (Fin q)]
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (J1 : Finset (Fin n)) (k : Fin q)
    (ha0 : ∀ i, 0 < a0 i) (hb : ∀ i, b i ≤ a0 i)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ m : ℤ, x j = (m : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    1 ≤ ∑ j ∈ J1, min ((a k j + a0 k - b k) / a0 k) (BetaJUnstrengthened a a0 j) * x j +
      ∑ j ∈ Finset.univ \ J1, BetaJUnstrengthened a a0 j * x j := by sorry

end Disjunctive.MonoidalStrengthening

