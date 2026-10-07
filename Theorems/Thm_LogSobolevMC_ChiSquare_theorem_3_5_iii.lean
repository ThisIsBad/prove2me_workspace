import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem theorem_3_5_iii {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K) :
    ∀ t : ℝ, 0 < t → ∀ q : ℝ, 2 ≤ q →
      q - 1 ≤ Real.exp (2 * logSobolev K π * t) →
      ∀ f : V → ℝ, lpNorm π q (heatOp K t f) ≤ lpNorm π 2 f := by sorry

end LogSobolevMC.ChiSquare

