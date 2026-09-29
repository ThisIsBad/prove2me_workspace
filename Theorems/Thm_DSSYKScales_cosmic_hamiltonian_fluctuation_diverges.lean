import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem cosmic_hamiltonian_fluctuation_diverges (N q : ℕ → ℕ) (lam J : ℝ) (hJ : J ≠ 0)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => cosmicHamiltonianSecondMoment (N n) (q n) J / (N n : ℝ))
      atTop (𝓝 (J ^ 2 * Real.exp (-(lam / 2)))) ∧
    Tendsto (fun n => cosmicHamiltonianSecondMoment (N n) (q n) J) atTop atTop := by sorry
end DSSYKScales
