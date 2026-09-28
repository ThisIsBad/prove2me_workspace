import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro

theorem aux_tsq_key (x s : ℂ) (hx : x ≠ 0) (h1 : 1 - x ^ 2 ≠ 0) :
    32 * (Real.pi : ℂ) ^ 4 * (s / (x - x⁻¹)) ^ 2 =
      ((Real.pi : ℂ) ^ 4 / 2) * (8 * x * s / (1 - x ^ 2)) ^ 2 := by
  have h2 : x - x⁻¹ = -(1 - x ^ 2) / x := by
    field_simp
    ring
  rw [h2]
  field_simp
  ring

end DS3Micro

open DS3Micro

theorem solution :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ b : ℂ, InRegime b → CS2 b = c * tensionHat b ^ 2 := by
  refine ⟨(Real.pi : ℂ) ^ 4 / 2, ?_, ?_⟩
  · have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero (pow_ne_zero _ hpi) two_ne_zero
  · intro b hb
    obtain ⟨β, hβ, hb2⟩ := hb
    have hx : b ^ 2 ≠ 0 := by
      rw [hb2]
      exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hβ.ne')
    have h4 : b ^ 4 = (b ^ 2) ^ 2 := by ring
    have h1 : 1 - (b ^ 2) ^ 2 ≠ 0 := by
      rw [hb2]
      intro h
      have h' : (1 - (Complex.I * (β : ℂ)) ^ 2) = ((1 + β ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [h'] at h
      have : (1 + β ^ 2 : ℝ) = 0 := by exact_mod_cast h
      nlinarith
    unfold CS2 tensionHat
    rw [h4, mul_assoc (8 * b ^ 2)]
    exact aux_tsq_key _ _ hx h1
