import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace ProcessingNetworks.PacketNetworks

/-- A point `t ≥ 0` is regular for a fluid limit path `(D̂,T̂,Ẑ)` (the sentence just before
Lemma 12.20, p. 241, PDF p. 257) if the path is differentiable at `t`: `D̂`, `Ẑ` and each `T̂ₛ`
(`s ∈ S`) differentiable at `t`, within the time domain `[0,∞)` (one-sided at `t = 0`, two-sided
elsewhere). -/
def RegularPoint {J : ℕ} (S : Finset (Fin J → ℕ)) {I : ℕ} (Dh : ℝ → Fin J → ℝ)
    (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ) (t : ℝ) : Prop :=
  DifferentiableWithinAt ℝ Dh (Set.Ici 0) t ∧
    (∀ s ∈ S, DifferentiableWithinAt ℝ (fun u => Th u s) (Set.Ici 0) t) ∧
    DifferentiableWithinAt ℝ Zh (Set.Ici 0) t

/-- The back-pressure fluid equation (12.44), Dai & Harrison p. 242 (PDF p. 258): at each regular
point `t ≥ 0`, `Ẑ(t)·R(d/dt)D̂(t) = max_{s∈⟨S⟩} Ẑ(t)·Rs`, phrased via the derivative vector `d` of
`D̂` at `t` (within `[0,∞)`) and via domination over `⟨S⟩` for the maximum. -/
def SatisfiesBackPressureFluidEquation {I J : ℕ} (dat : PacketNetworkData I J)
    (S : Finset (Fin J → ℕ)) (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ)
    (Zh : ℝ → Fin I → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → RegularPoint S Dh Th Zh t → ∀ d : Fin J → ℝ,
    HasDerivWithinAt Dh d (Set.Ici 0) t →
    ∃ shat ∈ hullFinset S,
      (∀ s' ∈ hullFinset S, Zh t ⬝ᵥ (R dat).mulVec s' ≤ Zh t ⬝ᵥ (R dat).mulVec shat) ∧
      Zh t ⬝ᵥ (R dat).mulVec d = Zh t ⬝ᵥ (R dat).mulVec shat

/-- A fluid model solution under the back-pressure control policy (Section 12.3, "Fluid
models", and Lemma 12.21): (12.31)-(12.36) plus the back-pressure fluid equation (12.44). -/
def IsBackPressureFluidModelSolution {I J : ℕ} (dat : PacketNetworkData I J)
    (S : Finset (Fin J → ℕ)) (lam : Fin I → ℝ) (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ)
    (Zh : ℝ → Fin I → ℝ) : Prop :=
  SatisfiesPacketFluidEquations dat S lam Dh Th Zh ∧
    SatisfiesBackPressureFluidEquation dat S Dh Th Zh

end ProcessingNetworks.PacketNetworks
