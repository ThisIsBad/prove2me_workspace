import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mixing
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem eq_2_8 {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : MarkovMixing.IsDist μ) :
    2 * MarkovMixing.tvDist μ π ^ 2 ≤ relEnt π μ ∧
      relEnt π μ ≤
        MarkovMixing.tvDist μ π + 1 / 2 * LogSobolevMC.ChiSquare.lpNorm π 2 (fun x => μ x / π x - 1) ^ 2 := by sorry

end LogSobolevMC.Entropy

