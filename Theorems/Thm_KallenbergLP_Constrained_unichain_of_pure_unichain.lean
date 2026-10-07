import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

/-- Kallenberg (1983), Lemma 4.6.1, p. 129: if the Markov chain induced by `P(f)` has at most one
ergodic set for every pure stationary `f^∞`, then the Markov chain induced by `P(π)` has at most
one ergodic set for every stationary `π^∞`. -/
theorem unichain_of_pure_unichain {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (hM : IsUnichain M)
    (π : KallenbergLP.AverageLP.Pair M → ℝ) (hπ : π ∈ StatRule M) :
    IsUnichainMatrix (policyMatrix π) := by sorry

end KallenbergLP.Constrained

