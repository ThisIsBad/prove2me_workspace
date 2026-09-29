import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- Lemma 5: `P*(i, j, k) ≥ k - μ_{i+k} + μ_i` if `i - j` is even, and
`P*(i, j, k) ≥ (μ_{i+k} - μ_i + μ_{j+k} - μ_j) π` if `i - j` is odd. -/
theorem Pstar_lower_bound (i j k : ℕ) :
    (Even ((i : ℤ) - j) →
      (k : ℝ) - (mu (i + k) : ℝ) + (mu i : ℝ) ≤ exPstar i j k) ∧
    (Odd ((i : ℤ) - j) →
      ((mu (i + k) : ℝ) - (mu i : ℝ) + (mu (j + k) : ℝ) - (mu j : ℝ)) * Real.pi
        ≤ exPstar i j k) := by sorry

end MasekPaterson.Necessity

