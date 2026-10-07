import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem entL_eq_relEnt {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (hf2 : LogSobolevMC.ChiSquare.lpNorm π 2 f = 1) :
    LogSobolevMC.ChiSquare.entL π f = relEnt π (fun x => f x ^ 2 * π x) := by sorry

end LogSobolevMC.Entropy

