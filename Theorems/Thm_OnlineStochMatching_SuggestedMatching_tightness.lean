import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

namespace OnlineStochMatching.SuggestedMatching

/-- The exact expectation and optimum for the complete-graph family in Section 4.1. -/
theorem tightness :
    ∀ (n : ℕ) (hn : 0 < n),
      let inst := completeInstance n hn
      ∀ (M : Finset (Fin n × Fin n)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option (Fin n)) (hlabel : IsLabelling inst M label),
        (∀ ω : Fin inst.n → inst.Copy, optimum inst ω = n) ∧
          expectedAlgorithm inst label =
            (n : ℝ) * (1 - (1 - 1 / (n : ℝ)) ^ n) := by sorry

end OnlineStochMatching.SuggestedMatching

