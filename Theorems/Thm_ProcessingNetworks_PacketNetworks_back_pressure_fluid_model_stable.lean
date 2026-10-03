import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPFluidModel

namespace ProcessingNetworks.PacketNetworks

/-- Lemma 12.21, Dai & Harrison p. 243 (PDF p. 259): if (12.26) is satisfied (`λ < Rŝ` for some
`ŝ ∈ ⟨S⟩`), then the fluid model defined by equations (12.31)-(12.36) and (12.44) is stable: there
is a `δ > 0` such that every fluid model solution has `Ẑ(t) = 0` for all `t ≥ δ`. -/
theorem back_pressure_fluid_model_stable
    {I J : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ)) (lam : Fin I → ℝ)
    (hload : ∃ shat ∈ hullFinset S, ∀ i, lam i < (R dat).mulVec shat i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ),
      IsBackPressureFluidModelSolution dat S lam Dh Th Zh →
      ∀ t : ℝ, δ ≤ t → Zh t = fun _ => 0 := by sorry

end ProcessingNetworks.PacketNetworks
