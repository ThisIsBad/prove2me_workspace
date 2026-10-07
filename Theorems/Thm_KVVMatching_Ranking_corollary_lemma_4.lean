import Definitions.Def_KVVMatching_Ranking_Algorithms

namespace KVVMatching.Ranking

/-- Corollary to Lemma 4, p. 354: expected matching cardinality in terms of
indices whose row and column are both covered. -/
theorem corollary_lemma_4 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hdiag : ∀ i, adj i i)
    (hupper : ∀ i j, adj i j → i ≤ j) :
    rowRankingExpectation adj = (n : ℝ) / 2 +
      (1 / 2 : ℝ) * ((n.factorial : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin n),
          ((doubleCovered (rowRankingMatching adj σ)).card : ℝ)) := by sorry

end KVVMatching.Ranking

