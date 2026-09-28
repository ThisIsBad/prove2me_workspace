import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- Display (12) of Vapnik and Chervonenkis (1971), p. 272, Subsection 6: the index of a
concatenated sample is at most the product of the indices of its two parts,
`Δ^S(x_1, ···, x_k, x_{k+1}, ···, x_l) ≤ Δ^S(x_1, ···, x_k) Δ^S(x_{k+1}, ···, x_l)`.
The two parts are `x : Fin k → X` and `y : Fin m → X` (so `l = k + m`), joined by `Fin.append`. -/
theorem eq12_index_append_le {X : Type*} (S : Set (Set X)) {k m : ℕ} (x : Fin k → X)
    (y : Fin m → X) :
    Shared.index S (Fin.append x y) ≤ Shared.index S x * Shared.index S y := by sorry

end VapnikChervonenkis.Entropy
