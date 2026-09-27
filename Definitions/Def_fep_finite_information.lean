import Definitions.Def_fep_finite_laws
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Tactic

/-!
# Finite information theory (mission substrate)

Transcribed from the proved module `FepSketches.finite_information` of the
fep_lean formalization (Active Inference Institute).  Entropy uses Mathlib's
continuous extension `Real.negMulLog`, so zero-mass atoms contribute exactly
zero.  Finite KL is represented by the nonnegative `klFun` integrand.
Normalization recovers separation even when the reference law has zero-mass
atoms; strict reference support is required only for the logarithmic
cross-entropy identity.
-/

namespace FreeEnergyPrinciple

open Finset InformationTheory
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Shannon entropy in nats, with the convention `0 log 0 = 0`. -/
noncomputable def entropy (p : FiniteLaw α) : ℝ :=
  ∑ x, Real.negMulLog (p x)

/-- Expected negative log score of `q` under `p`. -/
noncomputable def crossEntropy (p q : FiniteLaw α) : ℝ :=
  ∑ x, -(p x) * Real.log (q x)

/-- Finite KL divergence as a weighted sum of Mathlib's nonnegative `klFun`. -/
noncomputable def finiteKL (p q : FiniteLaw α) : ℝ :=
  ∑ x, q x * klFun (p x / q x)

/-- Finite Shannon entropy is nonnegative. -/
theorem entropy_nonneg (p : FiniteLaw α) : 0 ≤ entropy p := by
  exact Finset.sum_nonneg fun x _ =>
    Real.negMulLog_nonneg (p.nonneg x) (p.mass_le_one x)

/-- Finite KL is nonnegative, including at zero reference atoms under the
totalized real-division convention. -/
theorem finiteKL_nonneg (p q : FiniteLaw α) : 0 ≤ finiteKL p q := by
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (q.nonneg x)
      (klFun_nonneg (div_nonneg (p.nonneg x) (q.nonneg x)))

/-- A finite law has zero divergence from itself, including at zero atoms. -/
theorem finiteKL_self (p : FiniteLaw α) : finiteKL p p = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : p x = 0
  · simp [hx]
  · rw [div_self hx, klFun_one, mul_zero]

/-- Pointwise conversion from the `klFun` integrand to logarithmic scoring. -/
theorem weighted_klFun_eq_log_score {a b : ℝ} (hb : 0 < b) :
    b * klFun (a / b) =
      (-a * Real.log b - Real.negMulLog a) + (b - a) := by
  by_cases ha : a = 0
  · simp [ha, klFun_zero]
  · rw [klFun_apply, Real.negMulLog_eq_neg, Real.log_div ha (ne_of_gt hb)]
    field_simp [ne_of_gt hb]
    ring

/-- For normalized finite laws, totalized finite KL vanishes exactly at
equality, without any support assumption.  A zero divergence first forces
equality wherever the reference has positive mass.  Normalization then forces
the actual law to put zero mass on every zero-reference atom. -/
theorem finiteKL_eq_zero_iff (p q : FiniteLaw α) :
    finiteKL p q = 0 ↔ p = q := by
  classical
  constructor
  · intro hzero
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ =>
        mul_nonneg (q.nonneg y)
          (klFun_nonneg (div_nonneg (p.nonneg y) (q.nonneg y))))).mp hzero
    have heq_of_reference_ne_zero : ∀ x, q x ≠ 0 → p x = q x := by
      intro x hx
      have hterm := hterms x (Finset.mem_univ x)
      have hfun : klFun (p x / q x) = 0 :=
        (mul_eq_zero.mp hterm).resolve_left hx
      have hratio : p x / q x = 1 :=
        (klFun_eq_zero_iff (div_nonneg (p.nonneg x) (q.nonneg x))).mp hfun
      exact (div_eq_one_iff_eq hx).mp hratio
    have hsplit :
        (∑ x : α, p x) =
          (∑ x : α, if q x = 0 then p x else 0) +
            ∑ x : α, if q x ≠ 0 then p x else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : q x = 0 <;> simp [hx]
    have hpositiveMass :
        (∑ x : α, if q x ≠ 0 then p x else 0) = 1 := by
      calc
        (∑ x : α, if q x ≠ 0 then p x else 0) =
            ∑ x : α, if q x ≠ 0 then q x else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : q x = 0
              · simp [hx]
              · simp [hx, heq_of_reference_ne_zero x hx]
        _ = ∑ x : α, q x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : q x = 0 <;> simp [hx]
        _ = 1 := q.sum_one
    have hzeroReferenceMass :
        (∑ x : α, if q x = 0 then p x else 0) = 0 := by
      linarith [p.sum_one, hsplit, hpositiveMass]
    apply FiniteLaw.ext_mass
    funext x
    by_cases hx : q x = 0
    · have hzeroTerms := (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ => by
          by_cases hy : q y = 0
          · simpa [hy] using p.nonneg y
          · simp [hy])).mp hzeroReferenceMass
      simpa [hx] using hzeroTerms x (Finset.mem_univ x)
    · exact heq_of_reference_ne_zero x hx
  · intro hpq
    subst p
    exact finiteKL_self q

/-- Under full reference support, finite KL is cross-entropy minus entropy. -/
theorem finiteKL_eq_crossEntropy_sub_entropy (p q : FiniteLaw α)
    (hq : ∀ x, 0 < q x) :
    finiteKL p q = crossEntropy p q - entropy p := by
  simp_rw [finiteKL, weighted_klFun_eq_log_score (hq _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hnorm : (∑ i : α, (q.mass i - p.mass i)) = 0 := by
    rw [Finset.sum_sub_distrib, q.sum_one, p.sum_one, sub_self]
  rw [hnorm, add_zero]
  rfl

end FreeEnergyPrinciple
