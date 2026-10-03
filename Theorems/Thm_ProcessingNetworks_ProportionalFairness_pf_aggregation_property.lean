import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation

namespace ProcessingNetworks.ProportionalFairness

/-- Proposition 10.2, Dai & Harrison p. 192 (PDF p. 208): given `AllocSet = {x ≥ 0 : Gx ∈
TildeAllocSet}` (Eq. 10.21) for the demand-group assignment `grp` encoding `G`, and `y := Gz`
(Eq. 10.22, here `groupAggregate grp z`), the PF allocation splits as `ψ_i(z) = ψ̃_ℓ(y) · z_i/y_ℓ`
for each `i` in group `ℓ` (Eq. 10.24) — real division supplies the stated convention `0/0 = 0`
automatically. `Ã ⊂ ℝ^L_+` has the properties assumed of the allocation set in Section 10.1
(Section 10.3: "a set `Ã` that has all the properties assumed earlier for `A`"). -/
theorem pf_aggregation_property
    {I L : ℕ} (AllocSet : Set (Fin I → ℝ)) (TildeAllocSet : Set (Fin L → ℝ))
    (grp : Fin I → Fin L) (hdom : IsPFDomain TildeAllocSet)
    (hAllocSet : ∀ x : Fin I → ℝ,
      x ∈ AllocSet ↔ (∀ i, 0 ≤ x i) ∧ groupAggregate grp x ∈ TildeAllocSet)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) (i : Fin I) :
    psi AllocSet z i =
      psi TildeAllocSet (groupAggregate grp z) (grp i) * z i / groupAggregate grp z (grp i) := by sorry

end ProcessingNetworks.ProportionalFairness
