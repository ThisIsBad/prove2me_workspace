import Definitions.Def_KVVMatching_Ranking_Algorithms

namespace KVVMatching.Ranking

/-- Lemma 5, p. 354: RANKING's matching is at least as large as EARLY's. -/
theorem lemma_5 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hdiag : ∀ i, adj i i)
    (hupper : ∀ i j, adj i j → i ≤ j)
    (rowOrder : Equiv.Perm (Fin n)) :
    (earlyMatching adj rowOrder).card ≤ (rowRankingMatching adj rowOrder).card := by sorry

end KVVMatching.Ranking

