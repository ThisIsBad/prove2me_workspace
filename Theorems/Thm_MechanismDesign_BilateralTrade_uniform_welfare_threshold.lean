import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.15 (Example 3.4, p.74): with both values uniform on `[0, 1]`, a
welfare-maximizing mechanism exists among the well-defined, incentive-compatible, individually
rational and ex post budget balanced direct mechanisms, and a mechanism of that class maximizes
expected welfare in it if and only if, almost surely, trade takes place exactly when
`θ_B − θ_S > 1/4`. -/
theorem uniform_welfare_threshold :
    (∃ m : DirectMechanism uniformEnv, m.Admissible ∧ m.ExPostBB ∧
      ∀ m' : DirectMechanism uniformEnv, m'.Admissible → m'.ExPostBB → m'.welfare ≤ m.welfare) ∧
    ∀ m : DirectMechanism uniformEnv, m.Admissible → m.ExPostBB →
      ((∀ m' : DirectMechanism uniformEnv, m'.Admissible → m'.ExPostBB →
          m'.welfare ≤ m.welfare) ↔
        ∀ᵐ θ ∂uniformEnv.prior, m.q θ = if (1 : ℝ) / 4 < θ.2 - θ.1 then 1 else 0) := by sorry

end MechanismDesign.BilateralTrade

