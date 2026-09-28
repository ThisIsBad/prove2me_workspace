import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

namespace SupportVectorMachines.LossFunctions

theorem aux_l230_main (a t : ℝ) :
    (if a * sgn t ≤ 0 then |a| else 0) ≤ |a| * |t - sgn a| := by
  have hR : 0 ≤ |a| * |t - sgn a| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hsa : sgn a = -1 := by simp [sgn, ha]
    by_cases htt : t < 0
    · have hst : sgn t = -1 := by simp [sgn, htt]
      rw [hst, if_neg (by linarith)]
      exact hR
    · have hst : sgn t = 1 := by simp [sgn, htt]
      rw [hst, if_pos (by linarith), hsa]
      have h1 : 1 ≤ |t - -1| := by
        rw [abs_of_nonneg (by linarith)]; linarith
      calc |a| = |a| * 1 := by ring
        _ ≤ |a| * |t - -1| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  · subst ha
    simp
  · have hsa : sgn a = 1 := by simp [sgn, not_lt.mpr ha.le]
    by_cases htt : t < 0
    · have hst : sgn t = -1 := by simp [sgn, htt]
      rw [hst, if_pos (by linarith), hsa]
      have h1 : 1 ≤ |t - 1| := by
        rw [abs_of_neg (by linarith)]; linarith
      calc |a| = |a| * 1 := by ring
        _ ≤ |a| * |t - 1| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    · have hst : sgn t = 1 := by simp [sgn, htt]
      rw [hst, if_neg (by linarith)]
      exact hR

end SupportVectorMachines.LossFunctions

open SupportVectorMachines.LossFunctions

theorem solution (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (if (2 * η - 1) * sgn t ≤ 0 then |2 * η - 1| else 0) ≤
      |2 * η - 1| * |t - sgn (2 * η - 1)| :=
  aux_l230_main (2 * η - 1) t
