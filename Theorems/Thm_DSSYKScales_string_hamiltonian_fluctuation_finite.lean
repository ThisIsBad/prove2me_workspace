import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem string_hamiltonian_fluctuation_finite (N q : ℕ → ℕ) (lam J : ℝ)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => stringHamiltonianSecondMoment (N n) (q n) J)
      atTop (𝓝 (J ^ 2 * Real.exp (-(lam / 2)) / lam)) := by sorry
end DSSYKScales
