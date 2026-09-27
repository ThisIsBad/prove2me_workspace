import Mathlib

namespace HighDimProb.SparseRecovery

/-- The **Euclidean (`ℓ2`) norm** `‖v‖₂` of a vector `v : ι → ℝ` indexed by a finite type `ι`,
`Real.sqrt (∑ i, v i ^ 2)`. Stated on the plain function type `ι → ℝ` rather than
`EuclideanSpace ℝ ι` so that `l1Norm` and `l0Sparsity` (Section 10.3.1's `‖·‖₁`, `‖·‖₀`) can be
stated on the same underlying type — `EuclideanSpace`'s own `Norm` instance is fixed to the `ℓ2`
norm and cannot host the `ℓ1` norm needed for the optimization program (10.12)/(10.22) this
chapter's theorems quantify over. -/
noncomputable def l2Norm {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (v i) ^ 2)

end HighDimProb.SparseRecovery
