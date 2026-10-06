import Definitions.Def_OnlineRandomization_Simulation_Winning

namespace OnlineRandomization.Simulation

/-- Manuscript p. 10, proof of Theorem 2.1: if the request player cannot
force a bad finite play, the answer player has an online response strategy. -/
theorem not_winning_deterministic {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ)
    (h : ¬ IsWinning F α [] []) :
    ∃ D : DetAlg R A, IsCompetitive F α D := by sorry

end OnlineRandomization.Simulation

