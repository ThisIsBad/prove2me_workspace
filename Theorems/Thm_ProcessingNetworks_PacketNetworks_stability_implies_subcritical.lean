import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_MarkovianPolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Theorem 12.8, Dai & Harrison p. 234 (PDF p. 250). In a packet network satisfying the standing
Assumptions 12.1 and 12.4, with schedule set `S` derived from the link configurations via (12.10)
and primitives satisfying the standing stochastic assumptions of Section 12.1 with arrival rate
vector `λ`: if there is a Markovian control policy `f` under which `Z` is an irreducible, positive
recurrent Markov chain (`f` admissible and its DTMC, with one-step kernel `jump`, irreducible and
positive recurrent — `IsStableMarkovianPolicy`, Definition 12.3), then `λ` lies in the subcritical
region `Λ` of (12.24). -/
theorem stability_implies_subcritical
    {I J K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ))
    (hstable : IsStableMarkovianPolicy dat S P jump) :
    lam ∈ subcriticalRegion dat S cfg := by sorry

end ProcessingNetworks.PacketNetworks

