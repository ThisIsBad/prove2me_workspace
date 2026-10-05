import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Hamiltonian

namespace DemandResponse.FirstBest

/-- Proposition 2.1 (consumer's best response), with the closed form of `H_m` corrected beyond
`Amax` and the index range of `b̂` read as `j = 1, …, d`. -/
theorem prop2_1_best_response {N d : ℕ} (P : Params N d) :
    (∀ z : ℝ, aHat P z ∈ effortA P ∧ ∀ a ∈ effortA P,
      (∑ i, aHat P z i) * z + c1 P (aHat P z) ≤ (∑ i, a i) * z + c1 P a) ∧
    (∀ γ : ℝ, bHat P γ ∈ effortB P ∧ ∀ b ∈ effortB P,
      c2 P (bHat P γ) - γ * sigSq P (bHat P γ) ≤ c2 P b - γ * sigSq P b) ∧
    (∀ z : ℝ, Hm P z =
      muBar P * (min (xneg z) P.Amax * xneg z - min (xneg z) P.Amax ^ 2 / 2)) ∧
    (∀ γ : ℝ, Hv P γ = -(1 / 2) * (c2 P (bHat P γ) - γ * sigSq P (bHat P γ))) := by sorry

end DemandResponse.FirstBest

