import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Weighted_Run

open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Weighted

/-- **Theorem 3.4** (Alon, Awerbuch, Azar, Buchbinder, Naor 2009, p. 367). On the normalized
instance of p. 365 (`1 ≤ c_S ≤ m` and `c_S ≤ α` for every set), with `Copt` covering every
arriving element and `c(Copt) ≤ α`, and with `n, m` large in the sense the proof uses
(`n · n^(2/m) + n < n²`): every configuration the algorithm reaches on `σ` is a running state
(never `FAIL`) in which
(i) every element `j ∈ X` with `w_j ≥ 1` is covered, and
(ii) `∑_{S ∈ C} c_S ≤ 3 log n (1 + (1 + 1/n) α log(m² (1 + 1/n))) + 2 α log n`,
the explicit form of the paper's `(6 + o(1)) α log m log n`. -/
theorem theorem_3_4 {X T : Type*} [Fintype X] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance X T) (α : ℝ) (Copt : Finset T) (σ : List X)
    (hc_one : ∀ S, 1 ≤ inst.c S)
    (hc_m : ∀ S, inst.c S ≤ (Fintype.card T : ℝ))
    (hc_α : ∀ S, inst.c S ≤ α)
    (hcov : ∀ j ∈ σ, coveredBy inst Copt j)
    (hopt : ∑ S ∈ Copt, inst.c S ≤ α)
    (hsize : (Fintype.card X : ℝ) * (Fintype.card X : ℝ) ^ ((2 : ℝ) / (Fintype.card T : ℝ)) +
        (Fintype.card X : ℝ) < (Fintype.card X : ℝ) ^ 2)
    (c : Config X T) (hc : Reachable inst α σ c) :
    ∃ s : AlgState X T, c = .ok s ∧
      (∀ j : X, 1 ≤ elementWeight inst s.w j → coveredBy inst s.C j) ∧
      ∑ S ∈ s.C, inst.c S ≤
        3 * Real.log (Fintype.card X : ℝ) *
            (1 + (1 + 1 / (Fintype.card X : ℝ)) * α *
              Real.log ((Fintype.card T : ℝ) ^ 2 * (1 + 1 / (Fintype.card X : ℝ)))) +
          2 * α * Real.log (Fintype.card X : ℝ) := by sorry

end OnlineSetCover.Weighted

