import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model

namespace MetricalTaskSystem.Deterministic

/-- **Theorem 1.1** (Borodin–Linial–Saks 1992, p. 747). For any metrical task system `(S, d)`
with `n` states, the competitive ratio is `w(S, d) = 2n − 1`. -/
theorem competitiveRatio_eq {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsMetrical d) :
    competitiveRatio d = 2 * (Fintype.card S : ℝ) - 1 := by sorry

end MetricalTaskSystem.Deterministic

