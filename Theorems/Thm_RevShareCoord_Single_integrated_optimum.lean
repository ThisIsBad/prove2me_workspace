import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

namespace RevShareCoord.Single

/-- Sec. 2.1, Eq. (1), p. 6: the integrated channel has a unique optimal order quantity
`q_I` on `[0, ∞)`; it is positive and satisfies `R'(q_I) = c`, and it is the only positive
solution of `R'(q) = c`. -/
theorem integrated_optimum (M : Model) :
    ∃ qI : ℝ, 0 < qI ∧ M.R' qI = M.c ∧ IsMaxOn M.Pi (Set.Ici 0) qI ∧
      (∀ q : ℝ, 0 ≤ q → IsMaxOn M.Pi (Set.Ici 0) q → q = qI) ∧
      (∀ q : ℝ, 0 < q → M.R' q = M.c → q = qI) := by sorry

end RevShareCoord.Single

