import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced

namespace KannanLattice.Core

/-- Proposition 2.16 of Kannan (1987), p. 16, in existence form: every lattice `L(b)` has a basis
that is reduced in the sense of Definition 2.6 ((2.7) and (2.8)). (The paper exhibits the output
of its procedure SHORTEST.) -/
theorem exists_reduced_basis (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∃ b' : Fin m → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b' ∧ lattice b' = lattice b ∧ IsReduced b' := by sorry

end KannanLattice.Core

