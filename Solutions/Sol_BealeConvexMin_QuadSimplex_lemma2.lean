import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

theorem aux_bl2_e_zero {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p l : Fin (N + 1))
    (hlp : l ≠ p) (hl : ∀ k, k ≠ l → c k l = 0 ∧ c l k = 0) :
    pivotE (c p) p l = 0 := by
  have h := (hl p (Ne.symm hlp)).1
  simp [pivotE, hlp, h]

theorem aux_bl2_cprime_row_p {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p l : Fin (N + 1))
    (hlp : l ≠ p) (hl : ∀ k, k ≠ l → c k l = 0 ∧ c l k = 0) :
    pivotCPrime c p (c p) p l = 0 := by
  have he := aux_bl2_e_zero c p l hlp hl
  have h := (hl p (Ne.symm hlp)).1
  simp [pivotCPrime, hlp, h, he]

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem solution {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p l : Fin (N + 1))
    (hp : c p p ≠ 0) (hlp : l ≠ p) (hl : ∀ k, k ≠ l → c k l = 0 ∧ c l k = 0) :
    pivotE (c p) p l = 0 ∧
    ∀ k, k ≠ l → pivotC c p (c p) k l = 0 ∧ pivotC c p (c p) l k = 0 := by
  have he := aux_bl2_e_zero c p l hlp hl
  have hrow := aux_bl2_cprime_row_p c p l hlp hl
  refine ⟨he, fun k hk => ⟨?_, ?_⟩⟩
  · by_cases hkp : k = p
    · subst hkp
      simp [pivotC, hrow]
    · have hkl := (hl k hk).1
      have hpl := (hl p (Ne.symm hlp)).1
      simp [pivotC, hkp, pivotCPrime, hlp, hkl, he, hpl]
  · have hlk := (hl k hk).2
    have hlp' := (hl p (Ne.symm hlp)).2
    by_cases hkp : k = p
    · subst hkp
      simp [pivotC, hlp, pivotCPrime, hlp', he]
    · simp [pivotC, hlp, pivotCPrime, hkp, hlk, hlp', he]
