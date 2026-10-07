import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step 3, first bracket, p. 34: at Step 3 all zeros are covered, each starred zero is
covered by exactly one line, there are as many covered lines as starred zeros, the starred zeros
form a maximum set of independent zeros, and the covered lines form a minimum set of lines
containing all the zeros. -/
theorem step3_maximal_minimal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : Reachable A s) (hph : s.phase = Phase.step3) :
    CoversZeros s.A s.rowCov s.colCov ∧
    (∀ p ∈ s.starred, (p.1 ∈ s.rowCov ∧ p.2 ∉ s.colCov) ∨ (p.1 ∉ s.rowCov ∧ p.2 ∈ s.colCov)) ∧
    s.rowCov.card + s.colCov.card = s.starred.card ∧
    (IsIndepZeros s.A s.starred ∧ s.starred.card = maxIndepZeros s.A) ∧
    (∀ R C : Finset (Fin n), CoversZeros s.A R C →
      s.rowCov.card + s.colCov.card ≤ R.card + C.card) := by sorry

end MunkresAlg.Assignment

