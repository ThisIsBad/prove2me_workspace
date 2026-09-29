import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model

namespace SatiaLave.MaxMin

/-- Eq. (5), p. 730: for every policy `A` and every admissible choice `P` of nature, the
present-value equations `v_i = Σ_j p^A_ij (r^A_ij + β v_j)` have exactly one solution, and it is
`presentValue M A P`. -/
theorem eq5_presentValue_unique {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    SolvesEq5 M A P (presentValue M A P) ∧
      ∀ v : S → ℝ, SolvesEq5 M A P v → v = presentValue M A P := by sorry

end SatiaLave.MaxMin
