import Definitions.Def_KVVMatching_Ranking_GreedyRun

namespace KVVMatching.Ranking

/-- Lemma 2, p. 354: an arbitrary refusal rule cannot cover more girls. -/
theorem lemma_2 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (boyOrder girlRank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    ((greedyRun adj boyOrder girlRank refuse).image Prod.snd) ⊆
    ((greedyRun adj boyOrder girlRank (fun _ _ _ => false)).image Prod.snd) := by sorry

end KVVMatching.Ranking

