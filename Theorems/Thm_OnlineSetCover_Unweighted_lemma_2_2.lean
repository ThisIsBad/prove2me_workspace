import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Unweighted

/-- Lemma 2.2 (Alon et al. 2009, p. 364): in an iteration with a weight augmentation (the
arriving element `j` has `w_j < 1`, `k` is the minimal integer with `2^k w_j > 1`, and every set
containing `j` has its weight multiplied by `2^k`), there is a family `F` of at most `⌈4 ln n⌉`
sets containing `j` such that the potential after the iteration, with cover `𝒞 ∪ F` and the
augmented weights, is at most the potential before it. Weights are positive, as the algorithm
maintains. -/
theorem lemma_2_2 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (hw : ∀ S, 0 < w S)
    (cover : Finset T) (j : E) (k : ℕ)
    (hlt : elementWeight inst w j < 1)
    (hk : IsAugExponent (elementWeight inst w j) k) :
    ∃ F : Finset T, F ⊆ inst.elemSets j ∧ F.card ≤ setCap (Fintype.card E) ∧
      potential inst (augment inst w j k) (cover ∪ F) ≤ potential inst w cover := by sorry

end OnlineSetCover.Unweighted

