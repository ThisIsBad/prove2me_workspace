import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

namespace ProcessingNetworks.PacketNetworks

open Filter

/-- Theorem 12.13, Dai & Harrison p. 236 (PDF p. 252). Fix an admissible Markovian control policy
`f` (Section 12.3's standing assumption, with values in the schedule set `S`), a sample point
`ω ∈ Ω₁` (one at which the SLLN (12.29) holds for the arrival rate vector `λ`) and an unbounded set
`G ⊂ Z^I_+` (`hG`: `{|z| : z ∈ G}` is unbounded). There is a sequence `{zₗ} ⊂ G` with `|zₗ| → ∞` and
functions `D̂,T̂,Ẑ` such that the fluid-scaled raw processes converge to them u.o.c. (12.30), and
every such limit satisfies the fluid equations (12.31)-(12.36). -/
theorem fluid_limit_existence
    {I J : ℕ} {Ω : Type*} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (P : PacketPrimitives I J Ω) (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
    (lam : Fin I → ℝ) (ω : Ω) (hω : SLLNHoldsAt P lam ω)
    (G : Set (Fin I → ℕ)) (hG : ¬ BddAbove (sizeN '' G)) :
    (∃ zseq : ℕ → Fin I → ℕ, (∀ n, zseq n ∈ G) ∧ Tendsto (fun n => sizeN (zseq n)) atTop atTop ∧
      ∃ (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ),
        FluidScaledConverge dat P S ω zseq Dh Th Zh) ∧
    ∀ (zseq : ℕ → Fin I → ℕ) (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ)
      (Zh : ℝ → Fin I → ℝ), (∀ n, zseq n ∈ G) → Tendsto (fun n => sizeN (zseq n)) atTop atTop →
      FluidScaledConverge dat P S ω zseq Dh Th Zh →
      SatisfiesPacketFluidEquations dat S lam Dh Th Zh := by sorry

end ProcessingNetworks.PacketNetworks
