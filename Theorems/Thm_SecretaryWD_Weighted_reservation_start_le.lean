import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm

namespace SecretaryWD.Weighted

/-- Lemma 3.2: reservations above each class use no more goods than the optimum. -/
theorem reservation_start_le {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (π : Equiv.Perm (Fin n)) (τ : ℕ) (hτ : τ ≤ n) (i : ℤ) :
    reservationStart v π τ K i ≤ optimalStart (K := K) v i := by sorry

end SecretaryWD.Weighted

