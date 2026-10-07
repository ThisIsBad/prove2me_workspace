import Mathlib
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 3.1, p. 715: the two-point chain `K(−1, 1) = K(1, −1) = 1` on `{−1, 1}` has
stationary measure `π ≡ 1/2`, spectral gap `λ = 2` and log-Sobolev constant `α = λ/2 = 1`. -/
theorem example_3_1 :
    MarkovMixing.IsStationary swap2 (fun _ => (1 / 2 : ℝ)) ∧
    LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) = 2 ∧
    LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = LogSobolevMC.ChiSquare.gap swap2 (fun _ => (1 / 2 : ℝ)) / 2 ∧
    LogSobolevMC.ChiSquare.logSobolev swap2 (fun _ => (1 / 2 : ℝ)) = 1 := by sorry

end LogSobolevMC.Metropolis

