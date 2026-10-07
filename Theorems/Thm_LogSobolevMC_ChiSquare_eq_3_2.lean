import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem eq_3_2 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) (hf : ∀ x, 0 < f x)
    (p : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hp : 1 ≤ p t)
    (p' : ℝ) (hp' : HasDerivAt p p' t) :
    let F := fun s : ℝ => lpNorm π (p s) (heatOp K s f)
    HasDerivAt F
      (F t ^ (-(p t) + 1) *
        (p' / (p t) ^ 2 * entLp π (p t) (heatOp K t f) -
          dirichlet K π (heatOp K t f)
            (fun x => heatOp K t f x ^ (p t - 1)))) t := by sorry

end LogSobolevMC.ChiSquare

