import Mathlib

namespace FoundationsML.MaxEnt

/-- The partition function `Z(w)` of a Gibbs distribution with prior `p0`, feature map `Φ`,
and parameter `w` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, Eq. (12.9), p. 300, PDF p. 317): `Z(w) = ∑_{x∈X} p0(x) exp(w·Φ(x))`. -/
noncomputable def PartitionFunction {X : Type*} [Fintype X] {N : ℕ}
    (p0 : X → ℝ) (Φ : X → Fin N → ℝ) (w : Fin N → ℝ) : ℝ :=
  ∑ x, p0 x * Real.exp (∑ j, w j * Φ x j)

end FoundationsML.MaxEnt
