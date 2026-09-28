import Mathlib

namespace FoundationsML.Regression

/-- The empirical loss (error) of a regression hypothesis `h : X → ℝ` on a labeled sample
`S : Fin m → X × ℝ` with respect to a loss function `L : ℝ → ℝ → ℝ` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (11.2), p. 268, PDF
p. 285): `R̂_S(h) = (1/m) ∑_{i=1}^m L(h(x_i),y_i)`. -/
noncomputable def EmpiricalError {X : Type*} {m : ℕ}
    (S : Fin m → X × ℝ) (L : ℝ → ℝ → ℝ) (h : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, L (h (S i).1) (S i).2

end FoundationsML.Regression
