import Mathlib

namespace HighDimProb.SparseRecovery

/-- The **`ℓ1` norm** `‖v‖₁` of a vector `v : ι → ℝ` indexed by a finite type `ι`, `∑ i, |v i|`.
Vershynin, *High-Dimensional Probability* (2018), Section 10.3.1's standing notation, used as the
objective of the recovery program (10.12) (`minimize ‖x'‖₁ s.t. y = Ax'`). -/
def l1Norm {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ∑ i, |v i|

end HighDimProb.SparseRecovery
