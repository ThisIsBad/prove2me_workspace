import Mathlib

namespace FoundationsML.MaxEnt

/-- The empirical average of the feature map `Φ` over a sample `S`, `E_{x∼D̂}[Φ(x)]` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, used from
Eq. (12.5)-(12.6), p. 298, PDF p. 315): `E_{x∼D̂}[Φ(x)]_j = (1/m) ∑_{i=1}^m Φ(x_i)_j`. -/
noncomputable def EmpiricalFeatureMean {X : Type*} {N m : ℕ}
    (Φ : X → Fin N → ℝ) (S : Fin m → X) : Fin N → ℝ :=
  fun j => (1 / (m : ℝ)) * ∑ i, Φ (S i) j

end FoundationsML.MaxEnt
