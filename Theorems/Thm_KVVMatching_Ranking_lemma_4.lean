import Definitions.Def_KVVMatching_Ranking_Algorithms

namespace KVVMatching.Ranking

/-- Lemma 4, p. 354: counting the vertices covered by a matching. -/
theorem lemma_4 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hdiag : ∀ i, adj i i)
    (hupper : ∀ i j, adj i j → i ≤ j)
    (M : Finset (Fin n × Fin n))
    (hM : IsMatching M)
    (hEdges : ∀ e ∈ M, adj e.1 e.2)
    (hCover : ∀ i : Fin n, firstMatched M i ∨ secondMatched M i) :
    (M.card : ℝ) = ((n : ℝ) + (doubleCovered M).card) / 2 := by sorry

end KVVMatching.Ranking

