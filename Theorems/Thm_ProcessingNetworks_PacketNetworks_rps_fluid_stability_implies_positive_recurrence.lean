import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPAmbientChain

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Theorem 12.27, Dai & Harrison p. 251 (PDF p. 267): in a fixed-routing packet network under the
chapter's standing assumptions (Assumptions 12.1 and 12.4, `S` from (12.10), primitives satisfying
Section 12.1's stochastic assumptions with arrival rate vector `λ`) operated under the random
proportional scheduler — `jump` being the one-step kernel of the DTMC `Z` it generates — if the
RPS fluid model is stable, then the DTMC `Z` is positive recurrent: on its state space `𝒳` of
states reachable from `0`, every state is recurrent with finite expected return time. -/
theorem rps_fluid_stability_implies_positive_recurrence
    {I K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (fr : FixedRoutingData I K) (h121 : SatisfiesAssumption121 fr.dat)
    (h124 : SatisfiesAssumption124 fr.cfg)
    (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain fr.dat P jump)
    (hstable : RPSFluidStable fr S lam) :
    PositiveRecurrentOn jump (reachableFrom jump 0) := by sorry

end ProcessingNetworks.PacketNetworks

