import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_RefinedLowerBound

namespace IgnallSchrage.Makespan

/-- p. 409: the refined bound used in the 3-machine computations is still a lower bound: for a
node `J = J_r` with `r < n` and every full sequence `σ` beginning with `J_r`, the refined bound
is at most the makespan of `σ`. -/
theorem refinedLowerBound_le_makespan {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n))
    (hJ : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : BeginsWith σ J) :
    refinedLowerBound a b c J ≤ makespan a b c σ := by sorry

end IgnallSchrage.Makespan

