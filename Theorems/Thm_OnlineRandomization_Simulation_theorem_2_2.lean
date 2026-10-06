import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- Manuscript p. 10, Theorem 2.2. -/
theorem theorem_2_2 {R A Ω Ω' : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (F : Game R A) (α β : ℝ → ℝ)
    (hα : IsLinear α) (hαmono : Monotone α) (hβ : IsLinear β)
    (G : RandAlg R A Ω) (H : RandAlg R A Ω')
    (hG : IsCompetitiveOnline F α G)
    (hH : IsCompetitiveObl F β H) :
    IsCompetitiveOffline F (α ∘ β) G := by sorry

end OnlineRandomization.Simulation

