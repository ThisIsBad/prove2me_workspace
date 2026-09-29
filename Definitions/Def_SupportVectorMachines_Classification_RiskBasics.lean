import Mathlib

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- A loss function (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22, restated locally per Hard Rule 9), represented as a curried function
`X → ℝ → ℝ → ℝ`. -/
abbrev Loss (X : Type*) : Type _ := X → ℝ → ℝ → ℝ

/-- The `L`-risk of `f` with respect to a distribution `P` on `X × ℝ` (Definition 2.2, p. 22):
`R_{L,P}(f) := ∫_{X×Y} L(x,y,f(x)) dP(x,y)`, as an ordinary (junk-at-non-integrable) Bochner
integral. -/
noncomputable def risk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ))
    (f : X → ℝ) : ℝ :=
  ∫ p, L p.1 p.2 (f p.1) ∂P

/-- The Bayes (minimal) `L`-risk with respect to `P` (Definition 2.3, p. 22-23):
`R*_{L,P} := inf { R_{L,P}(f) : f : X → ℝ measurable }`. -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    ℝ :=
  sInf {r : ℝ | ∃ f : X → ℝ, Measurable f ∧ risk L P f = r}

end SupportVectorMachines.Classification
