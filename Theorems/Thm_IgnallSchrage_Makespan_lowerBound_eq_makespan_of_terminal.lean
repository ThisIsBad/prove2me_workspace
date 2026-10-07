import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound

namespace IgnallSchrage.Makespan

/-- General form of p. 403 ("node 231's lower bound, which is the makespan for sequence 2314"):
for a node `J = J_{n-1}` with `n - 1` jobs, `LB(J_{n-1})` equals the makespan of the full
sequence `σ` that begins with `J_{n-1}` (i.e. `J_{n-1}` followed by its one unscheduled job). -/
theorem lowerBound_eq_makespan_of_terminal {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n))
    (hJ : J.length + 1 = n) (σ : Equiv.Perm (Fin n)) (hσ : BeginsWith σ J) :
    lowerBound a b c J = makespan a b c σ := by sorry

end IgnallSchrage.Makespan

