import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem lemma_2_6 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∀ p : ℝ, 2 ≤ p →
      2 / p * dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1))) ∧
    (MarkovMixing.DetailedBalance K π → ∀ p : ℝ, 1 < p →
      4 * (p - 1) / p ^ 2 *
          dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1))) := by sorry

end LogSobolevMC.ChiSquare

