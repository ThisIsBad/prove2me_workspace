import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem lemma_2_5 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x)
    (p : ℝ) (hp : 1 ≤ p) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    HasDerivWithinAt (fun t : ℝ => ∑ x, |heatOp K t f x| ^ p * π x)
      (-p * dirichlet K π f (fun x => f x ^ (p - 1))) (Set.Ici 0) 0 := by sorry

end LogSobolevMC.ChiSquare

