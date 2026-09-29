import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

namespace TSPHeuristics.Insertion

/-- Lemma 1, p. 565: if `d(p, q) ≥ min(l_p, l_q)` for all distinct nodes `p, q` and
`l_p ≤ OPTIMAL / 2` for all nodes `p`, then `Σ_p l_p ≤ ½(⌈lg n⌉ + 1) OPTIMAL`.
Condition a) is required for distinct nodes only (the page says "for all nodes p and q"; with
`p = q` it would force `l_p ≤ 0`, and the proof applies it only to edges of a tour). -/
theorem lemma_1_sum_le_half_clog_add_one_mul_optimal {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d) (l : Fin n → ℝ)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q)
    (hb : ∀ p, l p ≤ TSPHeuristics.Shared.optimal d / 2) :
    ∑ p, l p ≤ (1 / 2) * ((Nat.clog 2 n : ℝ) + 1) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.Insertion

