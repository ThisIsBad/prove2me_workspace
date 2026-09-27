import Mathlib

namespace FoundationsML.DimReduction

/-- The squared Euclidean norm `‖v‖²` of a vector `v ∈ ℝⁿ`, written coordinate-wise as a sum of
squares (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press
2018, §15.4, used throughout Lemmas 15.3-15.4, p. 354-355, PDF p. 371-372, e.g. `‖u−v‖²`,
`‖f(u)−f(v)‖²`): `‖v‖² = ∑_{i=1}^n v_i²`. -/
def SqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, (v i) ^ 2

end FoundationsML.DimReduction
