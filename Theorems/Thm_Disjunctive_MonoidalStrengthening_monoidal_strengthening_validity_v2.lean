import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic


namespace Disjunctive.MonoidalStrengthening

/-- Proposition 11.22 (Balas, *Disjunctive Programming*, Springer 2018, §11.9, p. 179-180).
Let `x ≥ 0` be integer on `J₁`, satisfy the background lower bounds `Σ_j a_ij x_j ≥ b_i`
(`i ∈ Q`), where — as in the book's setting — each bound is no larger than the corresponding
right-hand side, `b_i ≤ a_i0`, and satisfy the disjunction `∨_i (Σ_j a_ij x_j ≥ a_i0)`. Then for
any fixed `m^j ∈ M` (`j ∈ J₁`), `x` satisfies the strengthened disjunction (11.41)
`∨_i (Σ_{j∈J₁} (a_ij + (a_i0 - b_i) m^j_i) x_j + Σ_{j∉J₁} a_ij x_j ≥ a_i0)`.

Correction w.r.t. the retired version: the standing assumption `b_i ≤ a_i0` is now hypothesis
`hb`; without it a positive monoid entry multiplies the negative factor `a_i0 - b_i`. -/
theorem monoidal_strengthening_validity_v2 {q n : ℕ}
    (a : Fin q → Fin n → ℝ) (a0 b : Fin q → ℝ) (hb : ∀ i, b i ≤ a0 i) (J1 : Finset (Fin n))
    (m : Fin n → Fin q → ℤ) (hm_mem : ∀ j ∈ J1, (fun i => m j i) ∈ CutMonoid q)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_lb : ∀ i, b i ≤ ∑ j, a i j * x j)
    (hx_disj : ∃ i, a0 i ≤ ∑ j, a i j * x j) :
    ∃ i, a0 i ≤ ∑ j ∈ J1, (a i j + (a0 i - b i) * (m j i : ℝ)) * x j +
      ∑ j ∈ Finset.univ \ J1, a i j * x j := by sorry

end Disjunctive.MonoidalStrengthening

