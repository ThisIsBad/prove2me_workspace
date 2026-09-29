import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_GibbsDistribution

namespace FoundationsML.MaxEnt

/-- The Maxent dual objective `G` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Eq. (12.10), p. 300, PDF p. 317), for `w : Fin N → ℝ`:
`G(w) = (1/m) ∑_{i=1}^m log(p_w(x_i)/p0(x_i)) − λ‖w‖_1`. -/
noncomputable def MaxEntDualObjective {X : Type*} [Fintype X] {N m : ℕ}
    (p0 : X → ℝ) (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) (w : Fin N → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, Real.log (GibbsDistribution p0 Φ w (S i) / p0 (S i)) -
    lam * ∑ j, |w j|

end FoundationsML.MaxEnt
