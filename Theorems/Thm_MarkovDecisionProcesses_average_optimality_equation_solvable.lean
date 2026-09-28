import Definitions.Def_MarkovDecisionProcesses_AverageReward

namespace MarkovDecisionProcesses
theorem average_optimality_equation_solvable {S A : Type*} [Fintype S] [Nonempty S]
    [Fintype A] (M : StationaryMDP S A) (hM : IsUnichain M) :
    (∃ (g : ℝ) (h : S → ℝ), ∀ s, optimalityResidual M g h s = 0) ∧
      ∀ (g : ℝ) (h : S → ℝ) (g' : ℝ) (h' : S → ℝ),
        (∀ s, optimalityResidual M g h s = 0) →
          (∀ s, optimalityResidual M g' h' s = 0) → g = g' := by sorry
end MarkovDecisionProcesses

