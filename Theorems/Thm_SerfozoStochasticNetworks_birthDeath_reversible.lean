import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem birthDeath_reversible (lam mu : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (hmu : ∀ n, 0 < mu (n + 1)) :
    DetailedBalance (birthDeathRate lam mu) (birthDeathMeasure lam mu) ∧
      IsReversible (birthDeathRate lam mu) := by sorry

end SerfozoStochasticNetworks
