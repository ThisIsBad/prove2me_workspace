import Definitions.Def_MarkovDecisionProcesses_AverageReward

namespace MarkovDecisionProcesses
theorem average_optimality_bounds {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (g : ℝ) (h : S → ℝ) :
    ((∀ s, optimalityResidual M g h s ≤ 0) → ∀ s, optGainSup M s ≤ g) ∧
    ((∀ s, 0 ≤ optimalityResidual M g h s) →
      ∀ s, g ≤ (⨆ d : {d : S → A // ∀ s, d s ∈ M.admissible s},
                  gainInf (stationaryPolicy M d.1 d.2) s) ∧
        (⨆ d : {d : S → A // ∀ s, d s ∈ M.admissible s},
            gainInf (stationaryPolicy M d.1 d.2) s) ≤ optGainInf M s) ∧
    ((∀ s, optimalityResidual M g h s = 0) →
      ∀ s, optGainSup M s = g ∧ optGainInf M s = g) := by sorry
end MarkovDecisionProcesses

