import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step 3, pp. 34–35: at Step 3 the smallest non-covered element `h` exists and is positive;
the transformation decreases each non-covered element by `h`, increases each twice-covered element
by `h` and leaves each once-covered element unaltered; each starred and primed zero is
once-covered and is still a zero afterwards; and `n_{k+1} ≥ n_k`. -/
theorem step3_transformation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) :
    ∃ h : ℝ, 0 < h ∧ (∃ p, NonCovered s p ∧ s.A p.1 p.2 = h) ∧
      (∀ q, NonCovered s q → h ≤ s.A q.1 q.2) ∧
      (∀ p ∈ s.starred ∪ s.primed,
        (p.1 ∈ s.rowCov ∧ p.2 ∉ s.colCov) ∨ (p.1 ∉ s.rowCov ∧ p.2 ∈ s.colCov)) ∧
      ∀ t, Step s t →
        (∀ i j, i ∉ s.rowCov → j ∉ s.colCov → t.A i j = s.A i j - h) ∧
        (∀ i j, i ∈ s.rowCov → j ∈ s.colCov → t.A i j = s.A i j + h) ∧
        (∀ i j, (i ∈ s.rowCov ∧ j ∉ s.colCov) ∨ (i ∉ s.rowCov ∧ j ∈ s.colCov) →
          t.A i j = s.A i j) ∧
        (∀ p ∈ s.starred ∪ s.primed, t.A p.1 p.2 = 0) ∧
        maxIndepZeros s.A ≤ maxIndepZeros t.A := by sorry

end MunkresAlg.Assignment

