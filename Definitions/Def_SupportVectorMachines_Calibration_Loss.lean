import Mathlib

namespace SupportVectorMachines.Calibration

/-- A loss function (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22, restated locally per Hard Rule 9 rather than imported from the
`LossFunctions` chapter draft): given a measurable space `X` and closed label set `Y ⊂ ℝ`, a loss
is a measurable map `L : X × Y × ℝ → [0,∞)`. Here it is represented as a curried function
`X → ℝ → ℝ → ℝ` (the middle argument ranges over the ambient reals; hypotheses fixing it to the
relevant label set `Y` and its nonnegativity are supplied where a specific loss is used, not
baked into the type). -/
abbrev Loss (X : Type*) : Type _ := X → ℝ → ℝ → ℝ

end SupportVectorMachines.Calibration
