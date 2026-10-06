import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- Manuscript p. 13, Corollary 2.1. -/
theorem corollary_2_1 {R A Ω Ω' : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (F : Game R A) (α β : ℝ → ℝ)
    (hα : IsLinear α) (hαmono : Monotone α) (hβ : IsLinear β)
    (G : RandAlg R A Ω) (H : RandAlg R A Ω')
    (hG : IsCompetitiveOnline F α G)
    (hH : IsCompetitiveObl F β H) :
    ∃ D : DetAlg R A, IsCompetitive F (α ∘ β) D := by sorry

end OnlineRandomization.Simulation

