import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem aux_rc_natDegree : (Polynomial.X ^ 2 + 1 : Polynomial ℝ).natDegree = 2 := by
  compute_degree!

theorem aux_rc_not_top :
    Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)} ≠ ⊤ := by
  intro h
  rw [Ideal.span_singleton_eq_top] at h
  have h0 := Polynomial.natDegree_eq_zero_of_isUnit h
  rw [aux_rc_natDegree] at h0
  exact absurd h0 (by norm_num)

end Nullstellensatz

open Nullstellensatz

theorem solution :
    Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)} ≠ ⊤ ∧
      ¬ ∃ x : ℝ, ∀ f ∈ Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)}, f.eval x = 0 := by
  refine ⟨aux_rc_not_top, ?_⟩
  rintro ⟨x, hx⟩
  have h := hx _ (Ideal.subset_span (Set.mem_singleton _))
  simp at h
  nlinarith [sq_nonneg x]
