import Mathlib

namespace ServiceParts.StockLevels

theorem everett {X : Type*} (S : Set X) (f g : X → ℝ) (b θ : ℝ) (hθ : 0 ≤ θ)
    (x0 : X) (hx0 : x0 ∈ S)
    (hopt : ∀ x ∈ S, f x0 + θ * (g x0 - b) ≤ f x + θ * (g x - b)) :
    IsLeast (f '' {x | x ∈ S ∧ g x ≤ g x0}) (f x0) := by sorry

end ServiceParts.StockLevels

