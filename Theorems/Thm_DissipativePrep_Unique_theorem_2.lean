import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem theorem_2 {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) (E : ℝ)
    (hD : ∀ (ψ : EuclideanSpace ℂ (Fin d)) (E' : ℝ), ψ ≠ 0 → (∀ l, act (c l) ψ = 0) →
      act H ψ = (E' : ℂ) • ψ → E' = E)
    (hS : ∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin d)), lazy c S → ¬ S ≤ (darkSpace H c E)ᗮ) :
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ, stationary (krausData H hH c g) ρ →
      densitySupport ρ ≤ darkSpace H c E := by sorry

end DissipativePrep.Unique

