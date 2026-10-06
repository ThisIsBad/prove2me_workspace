import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm

namespace SecretaryWD.Weighted

/-- Lemma 3.3: each class with at least two optimum goods retains an eighth of its value. -/
theorem reserved_class_value {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (i : ℤ) (hi : 2 ≤ optimalClassCount (K := K) v i) :
    optimalClassValue v w i / 8 ≤ expectedReservedClassValue v w i := by sorry

end SecretaryWD.Weighted

