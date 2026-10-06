import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Theorem A.1, oracle-access clause (PDF p. 9): Algorithm 4 (MultilinearUSM), run on a
nonnegative submodular `f` in any order `l = [u_1, …, u_n]` of the ground set, ends with
`x_n = y_n`, and its output, the random set `R(x_n)`, has expected value
`F(x_n) ≥ f(OPT)/2`, i.e. `f(OPT) ≤ 2 · F(x_n)`. -/
theorem multilinear_usm_half {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l) :
    (state f l l.length).1 = (state f l l.length).2 ∧
    NonmonotoneSubmod.Shared.OPT f
      ≤ 2 * NonmonotoneSubmod.Shared.F f (state f l l.length).1 := by sorry

end DoubleGreedyUSM.Fractional

