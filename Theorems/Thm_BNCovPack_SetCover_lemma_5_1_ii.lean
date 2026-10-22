import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_BNCovPack_SetCover_Potential

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- **Lemma 5.1 (ii)** (Buchbinder–Naor 2009, p. 12; proof p. 13): when the weight of a set `s`
is augmented by `δ ≥ 0`, either taking `s` to the cover or excluding it does not increase `Φ`
(compared with its value before the augmentation). Stated for every state `(w, C)` and every
`α ≥ 0`; the paper's proof assumes `δ ≤ 1` but does not use it. -/
theorem lemma_5_1_ii {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα : 0 ≤ α) (OPT : ℕ)
    (w : T → ℝ) (C : Finset T) (s : T) (δ : ℝ) (hδ : 0 ≤ δ) :
    potential inst α OPT (Function.update w s (w s + δ)) (insert s C) ≤ potential inst α OPT w C ∨
    potential inst α OPT (Function.update w s (w s + δ)) C ≤ potential inst α OPT w C := by sorry

end BNCovPack.SetCover

