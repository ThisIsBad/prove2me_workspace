import Definitions.Def_OnlineRandomization_Simulation_Winning

namespace OnlineRandomization.Simulation

/-- Manuscript p. 9, proof of Theorem 2.1, first paragraph. -/
theorem initial_position_iff {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) :
    IsWinning F α [] [] ↔
      ∃ Q : OfflineAdv R A, ∀ G : DetAlg R A,
        α (F.opt (play G Q).1) < F.cost (play G Q).1 (play G Q).2 := by sorry

end OnlineRandomization.Simulation

