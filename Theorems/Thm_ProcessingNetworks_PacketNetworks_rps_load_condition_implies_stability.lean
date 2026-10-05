import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPAmbientChain

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Theorem 12.28, Dai & Harrison p. 255 (PDF p. 271) — the goal theorem of this mission. In a
fixed-routing packet network under the chapter's standing assumptions (Assumptions 12.1 and 12.4,
`S` from (12.10), primitives satisfying Section 12.1's stochastic assumptions with arrival rate
vector `λ`), operated under the random proportional scheduler with `jump` the one-step kernel of
the DTMC `Z` it generates, assume the load condition (12.50): `ρ < ĉ` for some `ĉ ∈ ⟨C⟩`, where
`ρ = Aα` (12.49) and `α = R⁻¹λ`, i.e. `α = λ + P'α` (12.48). Then (a) the RPS fluid model is stable,
and hence (b) the DTMC `Z` is positive recurrent (on its state space `𝒳` of states reachable from
`0`). `hdom` records that `⟨C⟩` qualifies as the domain `Ã` of the PF fluid model of Section 10.4
(bounded, closed, convex, monotone, nontrivial), the standing assumption of Theorem 10.5 through
which the book proves (a); it holds when `C` is taken closed under decreasing a configuration. -/
theorem rps_load_condition_implies_stability
    {I K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (fr : FixedRoutingData I K) (h121 : SatisfiesAssumption121 fr.dat)
    (h124 : SatisfiesAssumption124 fr.cfg)
    (hdom : ProportionalFairness.IsPFDomain (hullFinset fr.cfg.C))
    (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain fr.dat P jump)
    (alpha : Fin I → ℝ) (halpha : ProportionalFairness.IsTotalArrivalRates (toPFData fr lam) alpha)
    (hload : ∃ chat ∈ hullFinset fr.cfg.C,
      ∀ k, ProportionalFairness.groupAggregate fr.linkDesig alpha k < chat k) :
    RPSFluidStable fr S lam ∧ PositiveRecurrentOn jump (reachableFrom jump 0) := by sorry

end ProcessingNetworks.PacketNetworks

