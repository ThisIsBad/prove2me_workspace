import Definitions.Def_OnlineRandomization_Simulation_Winning

namespace OnlineRandomization.Simulation

open MeasureTheory

/-- Manuscript pp. 9–10, proof of Theorem 2.1: strict pointwise defeat
persists under expectation because the adversary has finite depth and A is finite. -/
theorem winning_defeats_randomized {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (Q : OfflineAdv R A)
    (hQ : ∀ G : DetAlg R A,
      α (F.opt (play G Q).1) < F.cost (play G Q).1 (play G Q).2)
    (H : RandAlg R A Ω) :
    (∫ ω, α (F.opt (play (H.alg ω) Q).1) ∂H.μ) <
      (∫ ω, F.cost (play (H.alg ω) Q).1 (play (H.alg ω) Q).2 ∂H.μ) := by sorry

end OnlineRandomization.Simulation

