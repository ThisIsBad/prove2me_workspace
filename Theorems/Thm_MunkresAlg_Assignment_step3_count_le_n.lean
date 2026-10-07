import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, finiteness paragraph, p. 35: along any finite piece of a run starting at a reachable
state, if the maximal number of independent zeros is the same value `m` at every Step 3 state of
the piece, then Step 3 is applied at most `n` times in it. -/
theorem step3_count_le_n {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ss : List (State n))
    (hchain : List.IsChain Step ss) (hhead : ∀ s ∈ ss.head?, Reachable A s) (m : ℕ)
    (hm : ∀ s ∈ ss, s.phase = Phase.step3 → maxIndepZeros s.A = m) :
    (ss.filter (fun s => s.phase = Phase.step3)).length ≤ n := by sorry

end MunkresAlg.Assignment

