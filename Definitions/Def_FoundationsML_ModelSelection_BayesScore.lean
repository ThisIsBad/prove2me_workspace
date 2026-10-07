import Mathlib

namespace FoundationsML.ModelSelection

/-- The Bayes scoring function for a real-valued scoring problem with conditional label
probability `η(x) = P[y = +1 | x]` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Eq. (4.9), p. 74, PDF p. 91): `h*(x) = η(x) − 1/2`. -/
noncomputable def BayesScore {X : Type*} (η : X → ℝ) (x : X) : ℝ :=
  η x - 1 / 2

end FoundationsML.ModelSelection
