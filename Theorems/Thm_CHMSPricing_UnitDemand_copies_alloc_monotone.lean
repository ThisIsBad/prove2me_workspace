import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism

namespace CHMSPricing.UnitDemand

/-- App. B, proof of Lemma 3, p. 13: the allocation rule of `𝒜^copies` (which serves the copy
`j` exactly when `𝒜` allocates service `j`) is monotone non-decreasing in each `v_j`: raising
`v_j` within its support, all other values fixed, never withdraws service `j`. -/
theorem copies_alloc_monotone {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (A : MultiMechanism J m) (hA : IsTruthfulMulti D 𝒥 owner A)
    (v : J → ℝ) (hv : v ∈ typeSpace D) (j : J) (x y : ℝ)
    (hx : x ∈ Set.Icc (D j).lo (D j).hi) (hy : y ∈ Set.Icc (D j).lo (D j).hi) (hxy : x ≤ y)
    (hj : j ∈ A.alloc (Function.update v j x)) :
    j ∈ A.alloc (Function.update v j y) := by sorry

end CHMSPricing.UnitDemand

