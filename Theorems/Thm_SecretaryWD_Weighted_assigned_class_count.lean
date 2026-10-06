import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm

namespace SecretaryWD.Weighted

/-- Lemma 3.1: a class with at least two optimum goods fills a quarter of them in expectation. -/
theorem assigned_class_count {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (i : ℤ) (hi : 2 ≤ optimalClassCount (K := K) v i) :
    (optimalClassCount (K := K) v i : ℝ) / 4 ≤
      expectedAssignedClassCount (K := K) v i := by sorry

end SecretaryWD.Weighted

