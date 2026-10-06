import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Proof of Lemma A.2, Case 3, inequality (6) (PDF p. 10), for both `u_i ∉ OPT` (the case the
page writes out) and `u_i ∈ OPT` ("the proof for the other case is similar"): at an iteration `i`
of Algorithm 4 run on a submodular `f` in the order `l` of the ground set, with `a_i ≥ 0` and
`b_i > 0`, `F(OPT_{i−1}) − F(OPT_i) ≤ a_i b_i / (a_i + b_i)`. -/
theorem ineq6 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length)
    (ha : 0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega)))
    (hb : 0 < bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) :
    NonmonotoneSubmod.Shared.F f (optI O (state f l (i - 1)))
        - NonmonotoneSubmod.Shared.F f (optI O (state f l i))
      ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
          * bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))
        / (aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
            + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) := by sorry

end DoubleGreedyUSM.Fractional

