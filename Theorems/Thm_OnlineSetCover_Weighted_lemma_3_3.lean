import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Weighted

/-- **Lemma 3.3** (Alon, Awerbuch, Azar, Buchbinder, Naor 2009, p. 366). (1) For any weights `w`
with `w S ≥ 0`, any cover `C`, and any set `S` with `c_S ≤ α` (footnote 1, p. 367), the per-set
substep (a)–(c) for `S` does not fail, and the potential after it is at most the potential
before. (2) In particular, if every set costs at most `α`, the algorithm never reaches `FAIL`. -/
theorem lemma_3_3 {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (hα : 0 < α) :
    (∀ (w : T → ℝ) (C : Finset T) (S : T), 0 ≤ w S → inst.c S ≤ α →
        ∃ (w' : T → ℝ) (C' : Finset T), processSet inst α w C S = some (w', C') ∧
          potential inst w' C' α ≤ potential inst w C α) ∧
      ((∀ S, inst.c S ≤ α) → ∀ σ : List X, ¬ Reachable inst α σ (.fail : Config X T)) := by sorry

end OnlineSetCover.Weighted

