import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSResidualProcess
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel

namespace ProcessingNetworks.PacketNetworks

/-- Theorem 12.24, Dai & Harrison p. 251 (PDF p. 267): consider a fixed-routing packet network
(schedule set `S` from (12.10)) operating under the random proportional scheduler (the policy of
the primitives `P`). Let `{zₗ : ℓ ≥ 1} ⊂ Z^I_+` satisfy `|zₗ| ≥ ℓ²` (0-indexed, as in Lemma 12.23)
and let `Ω₂` be as in Lemma 12.23. For each `ω ∈ Ω₁ ∩ Ω₂` (`Ω₁`: the SLLN (12.29) holds at `ω`),
all fluid limits `(D̂,T̂,Ẑ)` in (12.30) along `{zₗ}` at `ω` satisfy the RPS fluid equation (12.65):
for each class `i` belonging to link `k`, `Ẑᵢ(t) > 0` implies
`(d/dt) D̂ᵢ(t) = (Ẑᵢ(t)/Ŷₖ(t)) ψₖ(Ŷ(t))`, where `Ŷ(t) = A Ẑ(t)` and `ψ(y)` solves (12.57). -/
theorem rps_fluid_drift_equation
    {I K : ℕ} {Ω : Type*} (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ))
    (hS : IsScheduleSet fr.cfg S) (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω)
    (hRPS : IsRPSPolicy fr S P.f)
    (zseq : ℕ → Fin I → ℕ) (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ))
    (ω : Ω) (hω1 : SLLNHoldsAt P lam ω) (hω2 : ω ∈ omega2 fr P zseq)
    (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hlim : FluidScaledConverge fr.dat P S ω zseq Dh Th Zh) :
    SatisfiesRPSFluidEquation fr Dh Zh := by sorry

end ProcessingNetworks.PacketNetworks

