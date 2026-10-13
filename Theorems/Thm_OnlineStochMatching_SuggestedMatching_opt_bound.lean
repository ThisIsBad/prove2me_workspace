import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Cut

namespace OnlineStochMatching.SuggestedMatching

/-- Section 4.1's high-probability bound on the hindsight optimum. -/
theorem opt_bound :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M),
        runProbability inst (fun ω =>
          (optimum inst ω : ℝ) ≤ (coveredAds M).card + ε * (inst.n : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ)) := by sorry

end OnlineStochMatching.SuggestedMatching

