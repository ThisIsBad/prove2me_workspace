import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem aloha_drift_positive (ν f : ℝ) (hν : 0 < ν) (hf : 0 < f) (hf1 : f < 1) :
    (∀ n : ℕ, 1 ≤ n → alohaSuccessProb ν f n
        = Real.exp (-ν) * ((n : ℝ) * f + (1 - f) * ν) * (1 - f) ^ (n - 1))
      ∧ Filter.Tendsto (fun n : ℕ => alohaSuccessProb ν f n) Filter.atTop (nhds 0)
      ∧ ∃ N : ℕ, ∀ n ≥ N, alohaSuccessProb ν f n < ν := by sorry

end KellyStochasticNetworks
