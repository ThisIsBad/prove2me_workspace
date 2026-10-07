import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound

namespace IgnallSchrage.Makespan

/-- p. 401: for a node `J = J_r` with `r < n` (so that `J̄_r` is nonempty), `LB(J_r)` is at most
the makespan of every full sequence `σ` that begins with `J_r`. -/
theorem lowerBound_le_makespan {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n))
    (hJ : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : BeginsWith σ J) :
    lowerBound a b c J ≤ makespan a b c σ := by sorry

end IgnallSchrage.Makespan

