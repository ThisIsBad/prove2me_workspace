import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step 2, second bracket, p. 34: after exchanging stars and primes along the sequence, the
starred zeros are independent zeros and there is one more of them. -/
theorem step2_starred_count {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s t : State n)
    (z₀ : Fin n × Fin n) (hs : Reachable A s) (hph : s.phase = Phase.step2 z₀)
    (hst : Step s t) :
    IsIndepZeros t.A t.starred ∧ t.starred.card = s.starred.card + 1 := by sorry

end MunkresAlg.Assignment

