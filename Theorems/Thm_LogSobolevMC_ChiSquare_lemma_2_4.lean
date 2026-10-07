import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem lemma_2_4 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (t : ℝ) (ht : 0 ≤ t) (f : V → ℝ) :
    lpNorm π 2 (fun x => heatOp K t f x - MarkovMixing.distExp π f) ^ 2 ≤
      Real.exp (-2 * t * gap K π) * MarkovMixing.distVar π f := by sorry

end LogSobolevMC.ChiSquare

