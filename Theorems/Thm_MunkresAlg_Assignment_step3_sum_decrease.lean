import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step D (p. 33) for the transformation of Step 3: the sum of the elements of the matrix
decreases by `n (n − n_k) h`, where `n_k` is the maximal number of independent zeros before the
transformation and `h` the smallest non-covered element. -/
theorem step3_sum_decrease {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s t : State n) (h : ℝ)
    (hs : Reachable A s) (hph : s.phase = Phase.step3)
    (hmin : ∃ p, NonCovered s p ∧ s.A p.1 p.2 = h) (hle : ∀ q, NonCovered s q → h ≤ s.A q.1 q.2)
    (hst : Step s t) :
    ∑ i, ∑ j, t.A i j =
      ∑ i, ∑ j, s.A i j - (n : ℝ) * ((n : ℝ) - (maxIndepZeros s.A : ℝ)) * h := by sorry

end MunkresAlg.Assignment

