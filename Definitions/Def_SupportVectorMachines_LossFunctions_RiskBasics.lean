import Mathlib

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- A loss function (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22): given a measurable space `X` and closed label set `Y ⊂ ℝ`, a loss is a
measurable map `L : X × Y × ℝ → [0,∞)`. Here it is represented as a curried function
`X → ℝ → ℝ → ℝ` (the middle argument ranges over the ambient reals; hypotheses fixing it to the
relevant label set `Y` and its nonnegativity are supplied where a specific loss is used, not
baked into the type). -/
abbrev Loss (X : Type*) : Type _ := X → ℝ → ℝ → ℝ

/-- The `L`-risk of `f` with respect to a distribution `P` on `X × ℝ` (Definition 2.2, p. 22):
`R_{L,P}(f) := ∫_{X×Y} L(x,y,f(x)) dP(x,y)`. -/
noncomputable def risk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ))
    (f : X → ℝ) : ℝ :=
  ∫ p, L p.1 p.2 (f p.1) ∂P

/-- The Bayes (minimal) `L`-risk with respect to `P` (Definition 2.3, p. 22-23):
`R*_{L,P} := inf { R_{L,P}(f) : f : X → ℝ measurable }`. The witness `f` is required to have an
`L`-integrable composition against `P`, so that the Bochner integral defining `risk L P f` is
never a junk (non-integrable) `0` masquerading as a genuine candidate risk. -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    ℝ :=
  sInf {r : ℝ | ∃ f : X → ℝ, Measurable f ∧
    Integrable (fun p : X × ℝ => L p.1 p.2 (f p.1)) P ∧ risk L P f = r}

end SupportVectorMachines.LossFunctions
