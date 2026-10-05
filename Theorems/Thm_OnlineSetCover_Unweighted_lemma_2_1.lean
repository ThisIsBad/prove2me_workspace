import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Unweighted

/-- Lemma 2.1 (Alon et al. 2009, p. 363): for every family `OPT` of sets covering every element
of the arrival list `σ`, every run of the unweighted algorithm on `σ` performs at most
`|OPT| · (log₂ m + 2)` weight augmentations, where `m` is the number of sets. -/
theorem lemma_2_1 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (σ : List E) (OPT : Finset T)
    (hOPT : ∀ j ∈ σ, coveredBy inst OPT j)
    (s : State T) (a : ℕ) (hrun : Run inst σ s a) :
    (a : ℝ) ≤ (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by sorry

end OnlineSetCover.Unweighted

