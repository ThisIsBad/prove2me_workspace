import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure

namespace IgnallSchrage.Makespan

/-- pp. 402–403, the example: for the 4-job jobset `a = (13, 7, 26, 2)`, `b = (3, 12, 9, 6)`,
`c = (12, 16, 7, 1)` (jobs `1, 2, 3, 4` of the paper are `0, 1, 2, 3` here), the run first has
a terminal node first on the list after 6 steps, that node is `231` (`[1, 2, 0]`), its lower
bound is `62`, the full sequence `2314` (the one sequence beginning with `[1, 2, 0]`) has
makespan `62`, and no sequence has makespan below `62`; so `2314` is optimal. -/
theorem example_run (a b c : Fin 4 → ℝ) (ha : a = ![13, 7, 26, 2]) (hb : b = ![3, 12, 9, 6])
    (hc : c = ![12, 16, 7, 1]) :
    (∀ k < 6, ∀ P, (run (lowerBound a b c) k).head? = some P → ¬ IsTerminal P) ∧
    (run (lowerBound a b c) 6).head? = some [1, 2, 0] ∧
    lowerBound a b c [1, 2, 0] = 62 ∧
    (∀ σ : Equiv.Perm (Fin 4), BeginsWith σ [1, 2, 0] → makespan a b c σ = 62) ∧
    ∀ σ : Equiv.Perm (Fin 4), 62 ≤ makespan a b c σ := by sorry

end IgnallSchrage.Makespan

