import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_PartitionFunction

namespace FoundationsML.MaxEnt

/-- The Gibbs distribution `p_w` with prior `p0`, parameter `w`, and feature vector `Φ` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Eq. (12.9), p. 300, PDF p. 317): `p_w(x) = p0(x) exp(w·Φ(x)) / Z(w)`. -/
noncomputable def GibbsDistribution {X : Type*} [Fintype X] {N : ℕ}
    (p0 : X → ℝ) (Φ : X → Fin N → ℝ) (w : Fin N → ℝ) (x : X) : ℝ :=
  p0 x * Real.exp (∑ j, w j * Φ x j) / PartitionFunction p0 Φ w

end FoundationsML.MaxEnt
