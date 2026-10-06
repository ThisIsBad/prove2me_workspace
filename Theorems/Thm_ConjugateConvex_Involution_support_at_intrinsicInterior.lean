import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75: `Γ` is not empty, and through every interior point `x°` of `G`
(read as a relative-interior point) there is a hyperplane of support with normal `(ξ, −1)`,
so that `φ(ξ) = Σx°ξ − f(x°)` for some `ξ ∈ Γ`. -/
theorem support_at_intrinsicInterior {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hG : G.Nonempty) (hf : ConvexOn ℝ G f) :
    (conjDomain G f).Nonempty ∧
      ∀ x₀ ∈ intrinsicInterior ℝ G,
        ∃ ξ ∈ conjDomain G f, conjFun G f ξ = x₀ ⬝ᵥ ξ - f x₀ := by sorry

end ConjugateConvex.Involution

