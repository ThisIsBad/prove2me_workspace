import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem density_measHeat {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (t : ℝ) :
    measHeat K t (fun x => f x * π x) =
      fun y => LogSobolevMC.ChiSquare.heatOp (MarkovMixing.timeReversal K π) t f y * π y := by sorry

end LogSobolevMC.Entropy

