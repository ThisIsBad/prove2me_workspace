import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism

namespace CHMSPricing.UnitDemand

/-- Theorem 13, p. 9: for an instance of the BSMD (regular distributions) whose feasibility
constraint is the intersection of two partition matroids, there are prices `p` such that
`ℛ^obl_p` `6.75`-approximates the optimal revenue: `ℛ^M ≤ (27/4)·ℛ^obl_p` for every truthful
mechanism `M`. -/
theorem two_partition_opm_approx {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β₁] [DecidableEq β₂]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ) :
    ∃ p : ι → ℝ, ∀ M : Mechanism ι,
      IsTruthful D (twoPartitionSystem part₁ cap₁ part₂ cap₂) M →
        revenue D M ≤ (27 / 4 : ℝ) * oblRevenue D (twoPartitionSystem part₁ cap₁ part₂ cap₂) p := by sorry

end CHMSPricing.UnitDemand

