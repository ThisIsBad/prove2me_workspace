import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- The book's sign convention, used throughout Section 2.3 (p. 36, proof of Lemma 2.30:
"let us first recall our convention `sign 0 := 1`"): agrees with the usual sign function except
that it sends `0` to `1` rather than `0`. -/
noncomputable def sgn (t : ℝ) : ℝ := if t < 0 then -1 else 1

/-- The clipped value of `t` at `±M` (Definition 2.22, Eq. (2.14), p. 34):
`clip M t = -M` if `t < -M`, `= t` if `t ∈ [-M,M]`, `= M` if `t > M`. -/
noncomputable def clip (M : ℝ) (t : ℝ) : ℝ :=
  if t < -M then -M else if t > M then M else t

/-- A loss `L` can be clipped at `M > 0` (Definition 2.22, p. 34) if clipping the prediction
never increases the loss: `L(x, y, clip M t) ≤ L(x, y, t)` for all `x, y, t`. -/
def CanBeClipped {X : Type*} (L : Loss X) (M : ℝ) : Prop :=
  ∀ x y t, L x y (clip M t) ≤ L x y t

/-- The classification loss `L_class` for standard binary classification (Example 2.4, Eq.
(2.2), p. 22): `L_class(y,t) := 1_{(-∞,0]}(y · sgn t)`, penalizing a prediction `t` whose sign
disagrees with the label `y`. Lifted to a full loss `X × Y × ℝ → [0,∞)` by ignoring `x`, per the
book's own identification convention (Definition 2.7). -/
noncomputable def classLoss {X : Type*} : Loss X := fun _ y t => if y * sgn t ≤ 0 then 1 else 0

/-- The hinge loss `L_hinge` (Example 2.27, p. 36): `L_hinge(y,t) := max{0, 1 - y·t}`, lifted to
a full loss `X × Y × ℝ → [0,∞)` as above. -/
noncomputable def hingeLoss {X : Type*} : Loss X := fun _ y t => max 0 (1 - y * t)

/-- The Bayes classification function `f*_{L_class,P}` associated to `η(x) := P(y=1|x)`
(Theorem 2.31, p. 37): `f*_{L_class,P}(x) := sign(2η(x) - 1)`. -/
noncomputable def bayesClassifier {X : Type*} (η : X → ℝ) (x : X) : ℝ := sgn (2 * η x - 1)

end SupportVectorMachines.LossFunctions
