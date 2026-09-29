import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The book's sign convention (p. 36, proof of Lemma 2.30: "let us first recall our convention
`sign 0 := 1`"): agrees with the usual sign function except that it sends `0` to `1`. -/
noncomputable def sgn (t : ℝ) : ℝ := if t < 0 then -1 else 1

/-- The classification loss `L_class` for standard binary classification `Y := {-1,1}` (Example
2.4, Eq. (2.2), p. 22): `L_class(y,t) := 1_{(-∞,0]}(y · sgn t)`, lifted to a full loss
`X × Y × ℝ → [0,∞)` by ignoring `x`. -/
noncomputable def classLoss {X : Type*} : Loss X := fun _ y t => if y * sgn t ≤ 0 then 1 else 0

/-- The hinge loss `L_hinge` (Example 2.27, p. 36): `L_hinge(y,t) := max{0, 1 - y·t}`, lifted to a
full loss `X × Y × ℝ → [0,∞)` as above. -/
noncomputable def hingeLoss {X : Type*} : Loss X := fun _ y t => max 0 (1 - y * t)

/-- The Bayes classification function `f*_{L_class,P}` associated to `η(x) := P(y=1|x)` (used in
Theorem 2.31, p. 37): `f*_{L_class,P}(x) := sign(2η(x) - 1)`. -/
noncomputable def bayesClassifier {X : Type*} (η : X → ℝ) (x : X) : ℝ := sgn (2 * η x - 1)

end SupportVectorMachines.Classification
