import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSResidualProcess

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Lemma 12.23, Dai & Harrison p. 251 (PDF p. 267): in a fixed-routing packet network with
schedule set `S` from (12.10), operated under the random proportional scheduler (the policy of the
primitives `P`, which satisfy Section 12.1's standing stochastic assumptions with arrival rate
vector `λ`), let `{zₗ : ℓ ≥ 1} ⊂ Z^I_+` be a sequence of initial states with `|zₗ| ≥ ℓ²` for each
`ℓ ≥ 1` (0-indexed: `(ℓ+1)² ≤ |zseq ℓ|`) and let `Ω₂` be the set of sample paths on which
`ξ^{zₗ}(|zₗ|,ω)/|zₗ| → 0`. Then `P(Ω₂) = 1` (12.64). -/
theorem rps_residual_slln
    {I K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (zseq : ℕ → Fin I → ℕ) (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ)) :
    ℙ (omega2 fr P zseq) = 1 := by sorry

end ProcessingNetworks.PacketNetworks

