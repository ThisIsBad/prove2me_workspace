import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Lemma A.2 (PDF p. 9): for Algorithm 4 run on a submodular `f` in the order `l` of the ground
set and `OPT_i = (OPT ∨ x_i) ∧ y_i`, for every `1 ≤ i ≤ n`,
`F(OPT_{i−1}) − F(OPT_i) ≤ 1/2 · [F(x_i) − F(x_{i−1}) + F(y_i) − F(y_{i−1})]`. -/
theorem lemma_A_2 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length) :
    NonmonotoneSubmod.Shared.F f (optI O (state f l (i - 1)))
        - NonmonotoneSubmod.Shared.F f (optI O (state f l i))
      ≤ 1 / 2 * (NonmonotoneSubmod.Shared.F f (state f l i).1
          - NonmonotoneSubmod.Shared.F f (state f l (i - 1)).1
          + NonmonotoneSubmod.Shared.F f (state f l i).2
          - NonmonotoneSubmod.Shared.F f (state f l (i - 1)).2) := by sorry

end DoubleGreedyUSM.Fractional

