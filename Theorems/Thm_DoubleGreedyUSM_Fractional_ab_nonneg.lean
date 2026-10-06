import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Proof of Lemma A.2, first sentence (PDF p. 9), citing Lemma II.1: for Algorithm 4 run on a
submodular `f` in the order `l = [u_1, …, u_n]` of the ground set, `a_i + b_i ≥ 0` at every
iteration `1 ≤ i ≤ n`, where `a_i = F(x_{i−1} + {u_i}) − F(x_{i−1})` and
`b_i = F(y_{i−1} − {u_i}) − F(y_{i−1})`. -/
theorem ab_nonneg {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length) :
    0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
      + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega)) := by sorry

end DoubleGreedyUSM.Fractional

