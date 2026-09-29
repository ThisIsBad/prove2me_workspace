import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_RademacherComplexity

open MeasureTheory

namespace FoundationsML.RademacherVC

/-- Theorem 3.3 (Rademacher-complexity generalization bound; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 31, PDF p. 48).
Let `G` be a family of measurable functions mapping from `Z` to `[0,1]`. Then, for any
`δ > 0`, with probability at least `1 − δ` over the draw of an i.i.d. sample `S` of size `m`,
each of the following holds for all `g ∈ G`:
`E[g(z)] ≤ (1/m) ∑_{i=1}^m g(z_i) + 2 R_m(G) + sqrt(log(1/δ)/(2m))`. -/
theorem rademacher_generalization_bound
    {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (G : Set (Z → ℝ)) (hGb : ∀ g ∈ G, ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hGm : ∀ g ∈ G, Measurable g)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → Z | ∀ g ∈ G, (∫ z, g z ∂D) ≤
        (1 / (m : ℝ)) * ∑ i, g (S i) + 2 * RademacherComplexity D G m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.RademacherVC

