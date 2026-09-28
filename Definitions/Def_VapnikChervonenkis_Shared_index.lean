import Mathlib

namespace VapnikChervonenkis.Shared

open Classical in
/-- The **index** `Δ^S(x_1, …, x_r)` of a class `S` of subsets of `X` with respect to a sample
`x = (x_0, …, x_{r-1})` (Vapnik and Chervonenkis 1971, p. 265, Subsection 1): the number of
different subsamples induced in the sample by the sets of `S`. The sample is a sequence
`x : Fin r → X` (repetitions allowed), and the subsample induced by `A` is recorded as the set of
positions `{i | x i ∈ A} : Finset (Fin r)`; `index S x` counts the distinct position sets arising
from some `A ∈ S`. -/
noncomputable def index {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) : ℕ :=
  (Finset.univ.filter (fun t : Finset (Fin r) => ∃ A ∈ S, ∀ i, i ∈ t ↔ x i ∈ A)).card

end VapnikChervonenkis.Shared
