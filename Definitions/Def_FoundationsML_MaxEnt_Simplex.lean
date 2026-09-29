import Mathlib

namespace FoundationsML.MaxEnt

/-- The simplex `Δ` of all probability distributions over a finite set `X` (Mohri, Rostamizadeh
& Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, §12.4, p. 299, PDF p.
316): `Δ = {p : X → ℝ | ∀x, p(x) ≥ 0, ∑_{x∈X} p(x) = 1}`. -/
def Simplex (X : Type*) [Fintype X] : Set (X → ℝ) :=
  {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1}

end FoundationsML.MaxEnt
