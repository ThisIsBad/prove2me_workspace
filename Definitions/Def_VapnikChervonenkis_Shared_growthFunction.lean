import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index

namespace VapnikChervonenkis.Shared

/-- The **growth function** `m^S(r) = max Δ^S(x_1, …, x_r)`, the maximum being taken over all
samples of size `r` (Vapnik and Chervonenkis 1971, p. 265, Subsection 1). The family of indices is
bounded by `2 ^ r`, so this supremum in `ℕ` is a genuine maximum whenever `X` is nonempty or
`r = 0`; for `X` empty and `r ≥ 1` there are no samples and the value is `0`. -/
noncomputable def growthFunction {X : Type*} (S : Set (Set X)) (r : ℕ) : ℕ :=
  ⨆ x : Fin r → X, index S x

end VapnikChervonenkis.Shared
