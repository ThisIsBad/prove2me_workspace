import Mathlib

open MeasureTheory

namespace FoundationsML.Regression

/-- The generalization error of a regression hypothesis `h : X → ℝ` with respect to a loss
function `L : ℝ → ℝ → ℝ` (curried form of `L : Y × Y → ℝ`, `L y y'` standing for `L(y,y')`)
and a joint distribution `D` on `X × ℝ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Eq. (11.1), p. 268, PDF p. 285):
`R(h) = E_{(x,y)∼D}[L(h(x),y)]`. -/
noncomputable def GeneralizationError {X : Type*} [MeasurableSpace X]
    (D : Measure (X × ℝ)) (L : ℝ → ℝ → ℝ) (h : X → ℝ) : ℝ :=
  ∫ p, L (h p.1) p.2 ∂D

end FoundationsML.Regression
