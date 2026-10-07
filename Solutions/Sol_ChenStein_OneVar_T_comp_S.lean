import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting



namespace ChenStein.OneVar

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

lemma S_zero (lam : ℝ≥0) (h : ℕ → ℝ) : S lam h 0 = 0 := by
  simp [S]

lemma S_succ (lam : ℝ≥0) (h : ℕ → ℝ) (n : ℕ) :
    S lam h (n + 1) = -((lam : ℝ)⁻¹) * (poissonPMFReal lam n)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), h k * poissonPMFReal lam k := by
  simp [S]

lemma pmf_succ (lam : ℝ≥0) (n : ℕ) :
    poissonPMFReal lam (n + 1) = (lam : ℝ) * poissonPMFReal lam n / (n + 1) := by
  unfold poissonPMFReal
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem T_comp_S_core (lam : ℝ≥0) (hlam : 0 < lam) (h : ℕ → ℝ) :
    ∀ w : ℕ, T lam (S lam h) w = h w := by
  intro w
  have hpos : ∀ n, 0 < poissonPMFReal lam n := fun n => poissonPMFReal_pos hlam
  have hlam' : (0 : ℝ) < lam := hlam
  unfold T
  rcases w with _ | n
  · rw [S_zero, S_succ]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    have h0 := hpos 0
    push_cast
    field_simp
    ring
  · rw [S_succ, S_succ, Finset.sum_range_succ _ (n + 1), pmf_succ]
    have h0 := hpos n
    push_cast
    field_simp
    ring

end ChenStein.OneVar

open ChenStein.OneVar
open scoped NNReal ENNReal

theorem solution (lam : ℝ≥0) (hlam : 0 < lam) (h : ℕ → ℝ) :
    ∀ w : ℕ, T lam (S lam h) w = h w := by
  exact T_comp_S_core lam hlam h
