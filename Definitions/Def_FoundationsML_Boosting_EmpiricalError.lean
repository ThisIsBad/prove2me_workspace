import Mathlib

namespace FoundationsML.Boosting

/-- The empirical (zero-one) error of a real-valued function `f : X → ℝ`, classified through
its sign against real-valued labels `y` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, proof of Theorem 7.2, p. 149, PDF p. 166):
`R̂_S(f) = (1/m) ∑_{i=1}^m 1_{y_i f(x_i) ≤ 0}`. -/
noncomputable def EmpiricalError {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (f : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, (if y i * f (S i) ≤ 0 then (1 : ℝ) else 0)

end FoundationsML.Boosting
