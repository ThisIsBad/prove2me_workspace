import Mathlib

namespace HighDimStat.SparseLinear

/-- The `ℓ∞`-norm of a vector `v ∈ ℝ^d`, `‖v‖∞ := maxⱼ |vⱼ|`, as used in the regularization
condition `λₙ ≥ 2‖Xᵀw/n‖∞` of Wainwright, *High-Dimensional Statistics* (2019), Theorem 7.13.
Realized as `⨆ j, |v j|` over the finite index type `Fin d`; for `d = 0` this is Mathlib's junk
value `0` for the supremum of the empty set (harmless: no vector exists at `d = 0` either). -/
noncomputable def linfNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ⨆ j, |v j|

end HighDimStat.SparseLinear
