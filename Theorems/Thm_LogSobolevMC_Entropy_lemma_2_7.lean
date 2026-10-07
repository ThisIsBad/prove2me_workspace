import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem lemma_2_7 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    2 * LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (f x)) ≤
        LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.log (f x)) f ∧
      (MarkovMixing.DetailedBalance K π →
        4 * LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (f x)) ≤
          LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.log (f x)) f) := by sorry

end LogSobolevMC.Entropy

