import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSRawModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

namespace ProcessingNetworks.PacketNetworks

/-- The RPS fluid equation (12.65), Dai & Harrison p. 251 (PDF p. 267): for each class `i`
belonging to link `k`, whenever `Ẑᵢ(t) > 0` the class-level departure rate is
`(d/dt) D̂ᵢ(t) = (Ẑᵢ(t)/Ŷₖ(t)) ψₖ(Ŷ(t))`, where `Ŷ(t) = A Ẑ(t)` and `ψ(y)` solves the RPS
optimization problem (12.57) (mission IX's `psi` over `⟨C⟩`; the coordinate `ψₖ(y)` is the
same for every solution when `yₖ > 0`). -/
def SatisfiesRPSFluidEquation {I K : ℕ} (fr : FixedRoutingData I K) (Dh Zh : ℝ → Fin I → ℝ) :
    Prop :=
  ∀ t : ℝ, 0 < t → ∀ i : Fin I, 0 < Zh t i →
    HasDerivAt (fun u => Dh u i)
      (Zh t i / ProportionalFairness.groupAggregate fr.linkDesig (Zh t) (fr.linkDesig i) *
        ProportionalFairness.psi (hullFinset fr.cfg.C)
          (ProportionalFairness.groupAggregate fr.linkDesig (Zh t)) (fr.linkDesig i)) t

/-- Definition 12.25, Dai & Harrison p. 251 (PDF p. 267): the RPS fluid model consists of the
general fluid equations (12.31)-(12.36) and the RPS fluid equation (12.65). -/
def IsRPSFluidModelSolution {I K : ℕ} (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ))
    (lam : Fin I → ℝ) (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ) :
    Prop :=
  SatisfiesPacketFluidEquations fr.dat S lam Dh Th Zh ∧ SatisfiesRPSFluidEquation fr Dh Zh

/-- Stability of the RPS fluid model (Theorems 12.27–12.28, "the RPS fluid model is stable"; the
chapter's notion, Definition 12.15's form, since (12.32) fixes `|Ẑ(0)| = 1`): there is a `δ > 0`
such that every RPS fluid model solution has `Ẑ(t) = 0` for all `t ≥ δ`. -/
def RPSFluidStable {I K : ℕ} (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ))
    (lam : Fin I → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ),
    IsRPSFluidModelSolution fr S lam Dh Th Zh → ∀ t : ℝ, δ ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.PacketNetworks
