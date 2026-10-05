import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_AmbientChain

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Theorem 12.10, Dai & Harrison p. 235 (PDF p. 251) — the goal theorem of this mission. Fix an
admissible Markovian control policy `f` (Section 12.3's standing assumption) in a packet network
satisfying Assumption 12.1, with primitives satisfying the standing stochastic assumptions of
Section 12.1 for the arrival rate vector `λ`, and let `jump` be the one-step kernel of the DTMC
`Z` under `f`. Assume `Z` is irreducible and the corresponding fluid limit (Definition 12.14) is
stable (Definition 12.15). Then `Z` is positive recurrent. The book's own proof "mimics that of
Theorem 6.2 and is thus omitted." -/
theorem fluid_limit_stability_implies_positive_recurrence
    {I J : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (S : Finset (Fin J → ℕ)) (lam : Fin I → ℝ)
    (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump)
    (hirr : Irreducible jump)
    (hstable : PacketFluidLimitStable dat P S lam) :
    PositiveRecurrent jump := by sorry

end ProcessingNetworks.PacketNetworks

