import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Proof of Theorem A.1, second display (PDF p. 9): for Algorithm 4 run on a nonnegative
submodular `f` in the order `l` of the ground set, with `n = l.length`,
`F(OPT_0) − F(OPT_n) ≤ 1/2 · [F(x_n) − F(x_0)] + 1/2 · [F(y_n) − F(y_0)] ≤ (F(x_n) + F(y_n))/2`. -/
theorem telescoped {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O) :
    NonmonotoneSubmod.Shared.F f (optI O (state f l 0))
        - NonmonotoneSubmod.Shared.F f (optI O (state f l l.length))
      ≤ 1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l l.length).1
            - NonmonotoneSubmod.Shared.F f (state f l 0).1)
        + 1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l l.length).2
            - NonmonotoneSubmod.Shared.F f (state f l 0).2) ∧
    1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l l.length).1
            - NonmonotoneSubmod.Shared.F f (state f l 0).1)
        + 1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l l.length).2
            - NonmonotoneSubmod.Shared.F f (state f l 0).2)
      ≤ (NonmonotoneSubmod.Shared.F f (state f l l.length).1
          + NonmonotoneSubmod.Shared.F f (state f l l.length).2) / 2 := by sorry

end DoubleGreedyUSM.Fractional

