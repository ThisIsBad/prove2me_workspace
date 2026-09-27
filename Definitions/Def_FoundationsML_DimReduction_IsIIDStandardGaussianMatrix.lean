import Mathlib

open MeasureTheory ProbabilityTheory

namespace FoundationsML.DimReduction

/-- A random matrix `A : Ω → Matrix (Fin k) (Fin N) ℝ` whose entries are sampled independently
from the standard normal distribution `N(0,1)` (Mohri, Rostamizadeh & Talwalkar, *Foundations
of Machine Learning*, 2nd ed., MIT Press 2018, Lemma 15.3, p. 355, PDF p. 372): every entry
`A_{ij}` has law `N(0,1)`, and the entries are (jointly) independent.

**Formalization Note.** Marginal law and independence are stated as two separate conjuncts,
following the book's own two-part phrasing ("entries... are sampled independently from the
standard normal distribution"); independence is expressed via `iIndepFun` over the product
index type `Fin k × Fin N`, matching the book's "for all `i, j`" scope exactly. -/
structure IsIIDStandardGaussianMatrix {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    {k N : ℕ} (A : Ω → Matrix (Fin k) (Fin N) ℝ) : Prop where
  isGaussian : ∀ i j, Measure.map (fun ω => A ω i j) Prob = gaussianReal 0 1
  indep : iIndepFun (fun (p : Fin k × Fin N) (ω : Ω) => A ω p.1 p.2) Prob

end FoundationsML.DimReduction
