import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_EmpiricalFeatureMean

namespace FoundationsML.MaxEnt

/-- The convex feature-constraint set `C` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 300, PDF p. 317): `C = {u : ‖u − E_{x∼D̂}[Φ(x)]
‖_∞ ≤ λ}`, written coordinate-wise. -/
def FeatureConstraintSet {X : Type*} {N m : ℕ}
    (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) : Set (Fin N → ℝ) :=
  {u | ∀ j, |u j - EmpiricalFeatureMean Φ S j| ≤ lam}

end FoundationsML.MaxEnt
