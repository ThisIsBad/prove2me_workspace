import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

/-- Proposition 1.9 of Kannan (1987), p. 8: a primitive vector `v` of the lattice `L(b)` (nonzero,
and `t • v ∉ L(b)` for every real `t ∈ (0, 1)`) belongs to some basis of the lattice. -/
theorem exists_basis_mem_of_primitive (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (v : EuclideanSpace ℝ (Fin k)) (hv : v ∈ lattice b) (hv0 : v ≠ 0)
    (hprim : ∀ t : ℝ, 0 < t → t < 1 → t • v ∉ lattice b) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧ v ∈ Set.range b' := by sorry

end KannanLattice.Core

