import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Weighted

/-- **Lemma 3.2** (Alon, Awerbuch, Azar, Buchbinder, Naor 2009, p. 366). Under the normalization
`1 ≤ c_S ≤ m` of p. 365, with `Copt` covering every arriving element and `c(Copt) ≤ α`: at every
running configuration reached by the algorithm, `∑_S w_S c_S ≤ 1 + N/n` (with `N` the number of
augmentation steps begun) and hence `∑_S w_S c_S ≤ 1 + (1 + 1/n) α log(m² (1 + 1/n))`, the
paper's `(2 + o(1)) α log m`. -/
theorem lemma_3_2 {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ))
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (s : AlgState X T) (hs : Reachable inst α σ (.ok s)) :
    ∑ S, s.w S * inst.c S ≤ 1 + (s.steps : ℝ) / (Fintype.card X : ℝ) ∧
      ∑ S, s.w S * inst.c S ≤
        1 + (1 + 1 / (Fintype.card X : ℝ)) * α *
          Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ))) := by sorry

end OnlineSetCover.Weighted

