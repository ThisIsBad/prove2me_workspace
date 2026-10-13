import Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins

namespace OnlineStochMatching.SuggestedMatching

/-- Fact 1, with the squared exponent established by its Appendix A proof. -/
theorem fact_1 (n : ℕ) (hn : 0 < n) (B : Finset (Fin n))
    (ε : ℝ) (hε : 0 < ε) :
    uniformProbability (fun ω : Fin n → Fin n =>
      (B.card : ℝ) * (1 - Real.exp (-1)) - ε * (n : ℝ) ≤
        (occupiedIn n B ω : ℝ) ∧
      (occupiedIn n B ω : ℝ) ≤
        (B.card : ℝ) *
          (1 - Real.exp (-1) + 1 / (Real.exp 1 * (n : ℝ))) + ε * (n : ℝ)) ≥
      1 - 2 * Real.exp (-(ε ^ 2) * (n : ℝ) / 2) := by sorry

end OnlineStochMatching.SuggestedMatching

