import Mathlib

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- The classification risk of a real-valued scoring function `h : X → ℝ` under the sign
convention `f_h(x) = +1` iff `h(x) ≥ 0`, expressed via the conditional label probability
`η(x) = P[y = +1 | x]` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*,
2nd ed., MIT Press 2018, p. 74, PDF p. 91, the derived form of `R(h) = E_{(x,y)∼D}[1_{f_h(x)≠y}]`
that the book establishes and uses throughout §4.7):
`R(h) = E_{x∼D_X}[η(x) 1_{h(x)<0} + (1 − η(x)) 1_{h(x)≥0}]`. -/
noncomputable def ScoringRisk {X : Type*} [MeasurableSpace X]
    (DX : Measure X) (η : X → ℝ) (h : X → ℝ) : ℝ :=
  ∫ x, (η x * (if h x < 0 then (1 : ℝ) else 0) +
    (1 - η x) * (if h x ≥ 0 then (1 : ℝ) else 0)) ∂DX

end FoundationsML.ModelSelection
