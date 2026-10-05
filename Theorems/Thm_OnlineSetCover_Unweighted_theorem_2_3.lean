import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Unweighted

/-- Theorem 2.3 (Alon et al. 2009, p. 364), with the explicit constant of its proof. Let the
instance have `n ≥ 2` elements and `m` sets, let `σ` be an arrival list and `OPT` any family of
sets covering every element of `σ`. Then
(a) the unweighted algorithm has a run on `σ` (an admissible choice exists at every step), and
(b) every run ends with a cover `𝒞` that covers every element of `σ` and satisfies
`|𝒞| ≤ ⌈4 ln n⌉ · |OPT| · (log₂ m + 2)`. -/
theorem theorem_2_3 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hn : 2 ≤ Fintype.card E)
    (σ : List E) (OPT : Finset T) (hOPT : ∀ j ∈ σ, coveredBy inst OPT j) :
    (∃ (s : State T) (a : ℕ), Run inst σ s a) ∧
      ∀ (s : State T) (a : ℕ), Run inst σ s a →
        (∀ j ∈ σ, coveredBy inst s.cover j) ∧
          (s.cover.card : ℝ) ≤
            (setCap (Fintype.card E) : ℝ) * (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by sorry

end OnlineSetCover.Unweighted

