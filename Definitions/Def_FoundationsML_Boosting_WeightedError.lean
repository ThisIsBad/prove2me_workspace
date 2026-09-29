import Mathlib

namespace FoundationsML.Boosting

/-- The distribution-weighted error of a base classifier `h : X → ℝ` on a labeled sample
`(S, y)` under a weighting `D : Fin m → ℝ` over the sample indices (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, §7.2, p. 147, PDF p.
164): `ε = P_{i∼D}[h(x_i) ≠ y_i] = ∑_{i=1}^m D(i)·1_{h(x_i)≠y_i}`, the weight AdaBoost places
on `h`'s errors under `D`. -/
noncomputable def WeightedError {X : Type*} {m : ℕ}
    (D : Fin m → ℝ) (S : Fin m → X) (y : Fin m → ℝ) (h : X → ℝ) : ℝ :=
  ∑ i, D i * (if h (S i) = y i then 0 else 1)

end FoundationsML.Boosting
