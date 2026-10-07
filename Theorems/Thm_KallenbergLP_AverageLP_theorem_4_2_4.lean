import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.2.4.** If `(x*, y*)` is an optimal solution of the linear program (4.2.11) such that
`(x*, y*)` is an extreme point of the set of feasible solutions, then the policy `f_*^∞`, where
`f_*(i) := a_i` such that `x*_{i a_i} > 0` for `i ∈ E_{x*}` and `y*_{i a_i} > 0` for
`i ∈ E ∖ E_{x*}`, is an average optimal policy.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 103, Theorem 4.2.4; `β_j > 0`, `Σ_j β_j = 1` from (4.2.10), p. 102.

**Formalization Note.** The conclusion has two parts: such an `f_*` exists (the book's "hence
the policy `f_*^∞` is well-defined", p. 103), and *every* `f_*` obeying the rule gives an average
optimal policy (Remark 4.2.4). Average optimality is `φ(f_*^∞) = φ` against all
history-dependent randomized policies. No unichain or ergodicity assumption is made. -/
theorem theorem_4_2_4 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z) :
    (∃ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf) ∧
    ∀ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf →
      IsAvgOptimal M (stationaryPolicy M f hf) := by sorry

end KallenbergLP.AverageLP

