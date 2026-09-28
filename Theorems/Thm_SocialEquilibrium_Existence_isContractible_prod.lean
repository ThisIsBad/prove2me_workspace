import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsContractible

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §1, p. 888: the product of two sets `X ⊆ ℝˡ`, `Y ⊆ ℝᵐ` deformable into the
points `x⁰ ∈ X`, `y⁰ ∈ Y` respectively is deformable into the point `(x⁰, y⁰)`. -/
theorem isContractible_prod {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} (x₀ : X) (y₀ : Y)
    (hX : IsDeformableInto X x₀) (hY : IsDeformableInto Y y₀) :
    IsDeformableInto (X ×ˢ Y) ⟨(x₀.1, y₀.1), x₀.2, y₀.2⟩ := by sorry

end SocialEquilibrium.Existence
