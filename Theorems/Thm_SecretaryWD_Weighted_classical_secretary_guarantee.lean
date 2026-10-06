import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm

namespace SecretaryWD.Weighted

/-- Section 2: the `⌊n/e⌋` observation rule selects the maximum with probability at least `1/e`. -/
theorem classical_secretary_guarantee {n : ℕ} (hn : 0 < n)
    (v : Fin n → ℝ) (hv : ∀ e, 0 ≤ v e) :
    1 / Real.exp 1 ≤
      orderAverage (fun π =>
        if ∃ t : Fin n,
            classicalSecretary n (fun s => (v (π s), π s)) = some t ∧
              valueRank v (π t) = 0 then (1 : ℝ) else 0) := by sorry

end SecretaryWD.Weighted

