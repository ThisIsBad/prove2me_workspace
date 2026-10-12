import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

namespace ManneLP.Equilibrium

theorem terminal_law_eq_7 (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    ∑ i ∈ states M, y i * trans M q i 0 = rhsZero M (jointLaw y q) ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ M.T →
      ∑ i ∈ states M, y i * trans M q i t = rhsPos M (jointLaw y q) t := by sorry

end ManneLP.Equilibrium

