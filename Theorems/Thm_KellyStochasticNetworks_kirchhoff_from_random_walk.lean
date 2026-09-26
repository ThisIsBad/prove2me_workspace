import Mathlib

namespace KellyStochasticNetworks

theorem kirchhoff_from_random_walk {n : ℕ} (γ : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (S : Finset (Fin n)) (hsym : ∀ i j, γ i j = γ j i)
    (hdeg : ∀ j, j ∉ S → 0 < ∑ k, γ j k)
    (hp : ∀ j, j ∉ S → p j = ∑ i, (γ j i / ∑ k, γ j k) * p i) :
    ∀ j, j ∉ S → (∑ i, γ i j * (p i - p j)) = 0 := by sorry

end KellyStochasticNetworks
