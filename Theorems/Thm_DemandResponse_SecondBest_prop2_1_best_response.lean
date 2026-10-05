import Mathlib
import Definitions.Def_DemandResponse_SecondBest_Hamiltonian

namespace DemandResponse.SecondBest

/-- Proposition 2.1 (arXiv:1810.09063v3, p. 9), with the closed form of `H_m` corrected beyond `A_max`
and the index range of `b̂` read as `j = 1, …, d`. -/
theorem prop2_1_best_response {N d : ℕ} (P : Params N d) :
    (∀ z : ℝ, ahat P z ∈ EffA P ∧
      ∀ a ∈ EffA P, (∑ i, ahat P z i) * z + c1 P (ahat P z) ≤ (∑ i, a i) * z + c1 P a) ∧
    (∀ γ : ℝ, bhat P γ ∈ EffB P ∧
      ∀ b ∈ EffB P, c2 P (bhat P γ) - γ * sigmaSq P (bhat P γ) ≤ c2 P b - γ * sigmaSq P b) ∧
    (∀ z : ℝ, Hm P z =
      muBar P * (min (negp z) P.Amax * negp z - min (negp z) P.Amax ^ 2 / 2)) ∧
    (∀ γ : ℝ, Hv P γ = -(1 / 2) * (c2hat P γ - γ * sigmaHatSq P γ)) := by sorry

end DemandResponse.SecondBest

