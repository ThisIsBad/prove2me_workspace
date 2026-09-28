import Definitions.Def_MarkovDecisionProcesses_AverageReward

namespace MarkovDecisionProcesses
theorem improving_rule_average_optimal {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (gstar : ℝ) (hstar : S → ℝ)
    (hB : ∀ s, optimalityResidual M gstar hstar s = 0)
    (d : S → A) (hd : IsImproving M hstar d) :
    IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1)) := by sorry
end MarkovDecisionProcesses

