import Definitions.Def_KVVMatching_Ranking_GreedyRun

namespace KVVMatching.Ranking

/-- The paper's RANKING matching: girls arrive in reverse index order, and
`boyRank r` is the boy of priority `r`, with priority zero highest. -/
noncomputable def rankingMatching {n : ℕ} (adj : Fin n → Fin n → Prop)
    (boyRank : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  (greedyRun (fun g b => adj b g) Fin.revPerm boyRank (fun _ _ _ => false)).image Prod.swap

/-- The dual rows-arrive version of RANKING, with the largest column index highest. -/
noncomputable def rowRankingMatching {n : ℕ} (adj : Fin n → Fin n → Prop)
    (rowOrder : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  greedyRun adj rowOrder Fin.revPerm (fun _ _ _ => false)

/-- EARLY: decline row `i` if column `i` was already matched by this run. -/
noncomputable def earlyMatching {n : ℕ} (adj : Fin n → Fin n → Prop)
    (rowOrder : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact greedyRun adj rowOrder Fin.revPerm
    (fun _ M i => decide (secondMatched M i))

/-- Uniform expected cardinality over the random ranking of boys. -/
noncomputable def rankingExpectation {n : ℕ} (adj : Fin n → Fin n → Prop) : ℝ :=
  ((n.factorial : ℝ)⁻¹) *
    ∑ π : Equiv.Perm (Fin n), ((rankingMatching adj π).card : ℝ)

/-- Uniform expected cardinality in the dual rows-arrive picture. -/
noncomputable def rowRankingExpectation {n : ℕ} (adj : Fin n → Fin n → Prop) : ℝ :=
  ((n.factorial : ℝ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin n), ((rowRankingMatching adj σ).card : ℝ)

/-- Uniform expected cardinality for EARLY over row arrival orders. -/
noncomputable def earlyExpectation {n : ℕ} (adj : Fin n → Fin n → Prop) : ℝ :=
  ((n.factorial : ℝ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin n), ((earlyMatching adj σ).card : ℝ)

/-- Indices whose row and column are both covered by a matching. -/
noncomputable def doubleCovered {n : ℕ} (M : Finset (Fin n × Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => firstMatched M i ∧ secondMatched M i)

end KVVMatching.Ranking
