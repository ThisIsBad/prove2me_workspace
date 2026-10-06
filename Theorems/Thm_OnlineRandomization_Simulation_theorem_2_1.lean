import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- Manuscript p. 9, Theorem 2.1. -/
theorem theorem_2_1 {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (hα : IsLinear α) (H : RandAlg R A Ω)
    (hH : IsCompetitiveOffline F α H) :
    ∃ D : DetAlg R A, IsCompetitive F α D := by sorry

end OnlineRandomization.Simulation

