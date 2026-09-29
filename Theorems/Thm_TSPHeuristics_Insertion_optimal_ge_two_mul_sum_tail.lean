import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- (2.1), p. 565: if the numbers `l` are non-increasing in the node label (the WLOG ordering
of the proof of Lemma 1) and satisfy condition a) of Lemma 1, then for every `1 ≤ k ≤ n`,
`OPTIMAL ≥ 2 Σ_{i=k+1}^{min(2k,n)} l_i`. Nodes are 0-based, so the paper's indices
`k+1, …, min(2k, n)` are `k, …, min(2k, n) - 1` here. -/
theorem optimal_ge_two_mul_sum_tail {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d)
    (l : Fin n → ℝ) (hl : Antitone l)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      2 * ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val ∧ i.val < min (2 * k) n), l i
        ≤ TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.Insertion
