import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.2.2.** The AMD-value-vector `φ` is the smallest AMD-superharmonic vector: `φ` is
AMD-superharmonic, and `φ ≤ φ̃` componentwise for every AMD-superharmonic `φ̃`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 99, Theorem 4.2.2.

**Formalization Note.** `φ_i = sup_R φ_i(R)` (`optGainInf`) is the supremum over all
history-dependent randomized policies of the lim inf average reward. -/
theorem theorem_4_2_2 (M : StationaryMDP S A) :
    IsAMDSuperharmonic M (optGainInf M) ∧
      ∀ φ' : S → ℝ, IsAMDSuperharmonic M φ' → ∀ i, optGainInf M i ≤ φ' i := by sorry

end KallenbergLP.AverageLP

