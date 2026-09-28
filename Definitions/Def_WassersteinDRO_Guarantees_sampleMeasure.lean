import Mathlib

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The law `P^N` of `N` iid training samples drawn from `P`, Kuhn et al. 2019, notation used
throughout Section 3 (e.g. Theorem 18, p. 22): the probability that an event holds for the
random sample sequence `(ξ̂_1,…,ξ̂_N)`, each `ξ̂_i` iid `~ P`, is computed under the product
measure on `Fin N → ℝ^m`. -/
noncomputable def sampleMeasure {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m))) (N : ℕ) :
    Measure (Fin N → EuclideanSpace ℝ (Fin m)) :=
  Measure.pi (fun _ : Fin N => P)

end WassersteinDRO.Guarantees
