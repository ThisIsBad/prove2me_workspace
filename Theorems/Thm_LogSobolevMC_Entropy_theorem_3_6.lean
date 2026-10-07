import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem theorem_3_6 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : MarkovMixing.IsDist μ) :
    (∀ t : ℝ, 0 < t →
        relEnt π (measHeat K t μ) ≤ relEnt π μ * Real.exp (-2 * LogSobolevMC.ChiSquare.logSobolev K π * t)) ∧
      (MarkovMixing.DetailedBalance K π → ∀ t : ℝ, 0 < t →
        relEnt π (measHeat K t μ) ≤
          relEnt π μ * Real.exp (-4 * LogSobolevMC.ChiSquare.logSobolev K π * t)) := by sorry

end LogSobolevMC.Entropy

