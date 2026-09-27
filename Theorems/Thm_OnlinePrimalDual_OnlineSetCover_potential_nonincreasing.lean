import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential

namespace OnlinePrimalDual.OnlineSetCover

/-- **Lemma 5.1** (p. 137, PDF p. 48) — the potential-function monotonicity Theorem 5.2 rests on.
Considers a step in which set `s`'s weight is augmented from `w s` to `w' s` (`w'` agreeing with
`w` off `s`), and the algorithm's actual choice of whether to add `s` to the cover: with
probability `p = 1 - n^{-2δs}` (`δs = w' s - w s`, the book's own probability, p. 137, "Add set
`s` to `C` with probability `1 − n^{−2δs}`", used in the proof's method-of-conditional-expectations
argument for the deterministic algorithm of p. 136-137's boxed description), the resulting expected
potential — the weighted average of `potential` with `s` inserted into `C` and `potential` with
`C` unchanged — never exceeds the potential before the step. When `s` is already in `C`,
`insert s C = C` and the statement degenerates to the book's other (deterministic) case, "the
first term of the potential function remains unchanged [and] the second term ... decreases"
(proof, p. 137), matching the lemma's own case-free statement. -/
theorem potential_nonincreasing {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα_pos : 0 < α)
    (w w' : T → ℝ) (C : Finset T) (s : T)
    (hw'_off : ∀ t, t ≠ s → w' t = w t) (hw'_ge : w s ≤ w' s)
    (hE : 1 ≤ Fintype.card E) :
    let n : ℝ := (Fintype.card E : ℝ)
    let p : ℝ := 1 - n ^ (-2 * (w' s - w s))
    p * potential inst w' (insert s C) α + (1 - p) * potential inst w' C α ≤
      potential inst w C α := by sorry

end OnlinePrimalDual.OnlineSetCover
