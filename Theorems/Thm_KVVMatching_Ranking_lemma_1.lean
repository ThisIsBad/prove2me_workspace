import Definitions.Def_KVVMatching_Ranking_GreedyRun

namespace KVVMatching.Ranking

/-- Lemma 1, p. 353: the duality principle for fixed orders. -/
theorem lemma_1 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (boyOrder girlOrder : Equiv.Perm (Fin n)) :
    (greedyRun (fun g b => adj b g) girlOrder boyOrder
      (fun _ _ _ => false)).image Prod.swap =
    greedyRun adj boyOrder girlOrder (fun _ _ _ => false) := by sorry

end KVVMatching.Ranking

