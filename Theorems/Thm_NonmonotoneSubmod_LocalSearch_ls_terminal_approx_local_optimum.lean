import Mathlib
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

/-- Feige–Mirrokni–Vondrák 2011, §3.1, p. 1141, sentence after Algorithm LS: if Algorithm LS has
terminated at `S` (no step 2 addition and no step 3 removal applies), then `S` is a
`(1 + ε/n²)`-approximate local optimum of `f` (Definition 3.2), where `n = |X|`. -/
theorem ls_terminal_approx_local_optimum {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ)
    (f : Finset X → ℝ) (S : Finset X) (hS : IsLSTerminal ε f S) :
    IsApproxLocalOptimum f (ε / (Fintype.card X : ℝ) ^ 2) S := by sorry

end NonmonotoneSubmod.LocalSearch
