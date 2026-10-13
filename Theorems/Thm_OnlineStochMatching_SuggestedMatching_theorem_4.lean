import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

namespace OnlineStochMatching.SuggestedMatching

/-- Theorem 4: additive high-probability guarantee and a complete-graph family
whose exact expected ratio approaches `1 - 1/e`. -/
theorem theorem_4 :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option A) (hlabel : IsLabelling inst M label),
        runProbability inst (fun ω =>
          (1 - Real.exp (-1)) * (optimum inst ω : ℝ) - ε * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ))) ∧
    (∀ (n : ℕ) (hn : 0 < n),
      let inst := completeInstance n hn
      ∀ (M : Finset (Fin n × Fin n)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option (Fin n)) (hlabel : IsLabelling inst M label),
        (∀ ω : Fin inst.n → inst.Copy, optimum inst ω = n) ∧
          expectedAlgorithm inst label =
            (n : ℝ) * (1 - (1 - 1 / (n : ℝ)) ^ n)) ∧
    Filter.Tendsto (fun n : ℕ => 1 - (1 - 1 / (n : ℝ)) ^ n)
      Filter.atTop (nhds (1 - Real.exp (-1))) := by sorry

end OnlineStochMatching.SuggestedMatching

