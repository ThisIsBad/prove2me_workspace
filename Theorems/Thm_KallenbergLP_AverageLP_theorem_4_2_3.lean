import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.2.3.** Let `f^∞` be any pure and stationary average optimal policy. Then
`φ̂(f^∞) ≥ φ̂(R)` for all `R ∈ C`, where `φ̂` is the lim sup average reward (4.2.9).

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 101, Theorem 4.2.3.

**Formalization Note.** Average optimality is the book's lim inf notion (`IsAvgOptimal`); `R`
ranges over all history-dependent randomized policies. -/
theorem theorem_4_2_3 (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (hopt : IsAvgOptimal M (stationaryPolicy M f hf)) :
    ∀ (R : AvgHRPolicy M) (i : S), gainSup R i ≤ gainSup (stationaryPolicy M f hf) i := by sorry

end KallenbergLP.AverageLP

