import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_PairwiseIncoherence
import Definitions.Def_HighDimStat_SparseLinear_RestrictedNullspaceProperty

namespace HighDimStat.SparseLinear

/-- **Proposition 7.9**, Wainwright, *High-Dimensional Statistics* (2019), Eq. (7.13), p. 203.
If the pairwise incoherence satisfies `δ_PW(X) ≤ 1/(3s)`, then the restricted nullspace
property holds for all subsets `S` of cardinality at most `s`. -/
theorem pairwise_incoherence_implies_restricted_nullspace {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (s : ℕ) (h : pairwiseIncoherence X ≤ 1 / (3 * (s : ℝ))) :
    ∀ S : Finset (Fin d), S.card ≤ s → RestrictedNullspaceProperty X S := by sorry

end HighDimStat.SparseLinear

