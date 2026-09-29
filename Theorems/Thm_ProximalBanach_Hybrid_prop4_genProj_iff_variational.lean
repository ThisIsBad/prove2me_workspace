import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition 4 (p. 941): in a smooth Banach space, for a convex `C`, `x ∈ E` and
`x₀ ∈ C`, `φ(x₀, x) = inf {φ(z, x) : z ∈ C}` (2.4) iff `⟨z - x₀, J x₀ - J x⟩ ≥ 0` for all
`z ∈ C` (2.5). -/
theorem prop4_genProj_iff_variational (hS : IsSmooth E) (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (C : Set E) (hcv : Convex ℝ C) (x x₀ : E)
    (hx₀ : x₀ ∈ C) :
    (∀ z ∈ C, phi J x₀ x ≤ phi J z x) ↔ ∀ z ∈ C, 0 ≤ (J x₀ - J x) (z - x₀) := by sorry

end ProximalBanach.Hybrid
