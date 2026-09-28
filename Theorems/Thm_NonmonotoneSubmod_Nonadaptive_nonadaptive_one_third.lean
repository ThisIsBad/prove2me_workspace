import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Nonadaptive_omega

namespace NonmonotoneSubmod.Nonadaptive

/-- Theorem 2.6 (Feige–Mirrokni–Vondrák 2011, p. 1139), in the explicit form of its proof
(p. 1140, last display). Let `f` be nonnegative and submodular on a nonempty ground set of
`n` elements. Let `ω̃` be any estimates with `|ω̃(x) − ω(x)| < OPT/n²` for all `x`, and
`A = {x : ω̃(x) > 0}`. Then the expected value of Algorithm NA, which returns `R = X(1/2)`
with probability 8/9 and `A` with probability 1/9, satisfies
`(8/9) E[f(X(1/2))] + (1/9) f(A) ≥ (1/3 − 4/(9n)) OPT`. -/
theorem nonadaptive_one_third {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (ωt : X → ℝ)
    (hωt : ∀ x, |ωt x - omega f x| < NonmonotoneSubmod.Shared.OPT f / (Fintype.card X : ℝ) ^ 2) :
    (1 / 3 - 4 / (9 * (Fintype.card X : ℝ))) * NonmonotoneSubmod.Shared.OPT f ≤
      (8 / 9) * NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) + (1 / 9) * f (Finset.univ.filter (fun x => 0 < ωt x)) := by sorry

end NonmonotoneSubmod.Nonadaptive

