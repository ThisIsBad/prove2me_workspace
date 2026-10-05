import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Weighted

/-- **Lemma 3.1** (Alon, Awerbuch, Azar, Buchbinder, Naor 2009, p. 365). Let every set cost at
least `1` (the normalization of p. 365) and let `Copt` cover every arriving element. At every
running configuration reached by the algorithm with guess `α` on `σ`, the number of weight
augmentation steps begun is at most `∑_{S ∈ Copt} (n c_S + 1) log(m² (1 + 1/n))`, and when
`c(Copt) ≤ α` this is at most `(n + 1) α log(m² (1 + 1/n))` (the paper's `(2 + o(1)) n α log m`).
Here `n = |X|`, `m = |T|`, natural logarithm. -/
theorem lemma_3_1 {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (s : AlgState X T) (hs : Reachable inst α σ (.ok s)) :
    (s.steps : ℝ) ≤
        ∑ S ∈ Copt, ((Fintype.card X : ℝ) * inst.c S + 1) *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) ∧
      ∑ S ∈ Copt, ((Fintype.card X : ℝ) * inst.c S + 1) *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) ≤
        ((Fintype.card X : ℝ) + 1) * α *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := by sorry

end OnlineSetCover.Weighted

