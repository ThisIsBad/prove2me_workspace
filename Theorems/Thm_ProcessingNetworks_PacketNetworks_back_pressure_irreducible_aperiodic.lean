import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_BackPressurePolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPAmbientChain
import Definitions.Def_ProcessingNetworks_PacketNetworks_MarkovianPolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Lemma 12.18, Dai & Harrison p. 241 (PDF p. 257): for a packet network satisfying (12.1) and
Assumption 12.1 (with the chapter's standing structure: `S` from (12.10) under Assumption 12.4,
primitives satisfying Section 12.1's standing assumptions, which include (12.1)), operating under
the back-pressure control policy `f` — `jump` being the one-step kernel of the DTMC `Z` generated
by `f` — the DTMC `Z` is irreducible and aperiodic: every state can reach `0`, and on the state
space `𝒳` of states reachable from `0` (the state space of the proof) the chain is irreducible and
aperiodic. -/
theorem back_pressure_irreducible_aperiodic
    {I J K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (hBP : IsBackPressurePolicy dat S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump) :
    (∀ z : Fin I → ℕ, (0 : Fin I → ℕ) ∈ reachableFrom jump z) ∧
      IrreducibleOn jump (reachableFrom jump 0) ∧
      AperiodicOn jump (reachableFrom jump 0) := by sorry

end ProcessingNetworks.PacketNetworks

