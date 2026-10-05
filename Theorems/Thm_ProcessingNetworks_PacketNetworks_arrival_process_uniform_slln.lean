import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Lemma 12.12, Dai & Harrison p. 236 (PDF p. 252): under the standing stochastic assumptions of
Section 12.1 (i.i.d. arrival vectors with mean `λ`), with probability one, for each `M > 0`,
`lim_{|z|→∞} sup_{0≤t≤M} |Êᶻ(t,ω) − λt| = 0` (Eq. 12.29), where `Êᶻ(t,ω) = |z|⁻¹ E(⌊|z|t⌋,ω)` —
the functional SLLN for the external arrival process `E`; `SLLNHoldsAt P lam ω` is (12.29) at
`ω`, with `|z| → ∞` rendered as a limit in the real scaling parameter directly. -/
theorem arrival_process_uniform_slln
    {I J : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (P : PacketPrimitives I J Ω) (lam : Fin I → ℝ) (hP : PrimitiveAssumptions P lam) :
    ∀ᵐ ω, SLLNHoldsAt P lam ω := by sorry

end ProcessingNetworks.PacketNetworks

