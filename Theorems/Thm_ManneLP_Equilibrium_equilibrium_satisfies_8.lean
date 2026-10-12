import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

namespace ManneLP.Equilibrium

theorem equilibrium_satisfies_8 (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ)
    (hq : IsRule M q) (hy : IsEquilibrium M q y) :
    (∀ a ∈ M.A, 0 ≤ jointLaw y q a) ∧ ∑ a ∈ M.A, jointLaw y q a = 1 ∧
      Eq80 M (jointLaw y q) ∧ ∀ t : ℕ, 1 ≤ t → t ≤ M.T → Eq8t M (jointLaw y q) t := by sorry

end ManneLP.Equilibrium

