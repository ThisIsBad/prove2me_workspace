import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

/-- Theorem (1.12) of Kannan (1987), p. 9, with the constant corrected from `½√m` to `√m`:
every `m`-dimensional lattice `L(b)` in `ℝᵏ` (`m ≥ 1`, `b` linearly independent) has a nonzero
vector of length at most `√m · d(L)^{1/m}`. -/
theorem exists_short_vector_sqrt_n (m k : ℕ) (hm : 1 ≤ m)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∃ v ∈ lattice b, v ≠ 0 ∧
      ‖v‖ ≤ Real.sqrt m * latticeDet b ^ ((1 : ℝ) / m) := by sorry

end KannanLattice.Core

