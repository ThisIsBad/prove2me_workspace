import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- Theorem 5.2 (first sentence), §5.3, pp. 42–43, read as an identity of feasible
sets: the constraints `aᵢᵀx ≥ bᵢ` (`i = 1, …, K`) hold for every perturbation
`[aᵢᵀ bᵢ]ᵀ + δᵢ` with `‖δᵢ‖₂ ≤ ρ` (each `δᵢ = (δaᵢ, δbᵢ) ∈ ℝ^{m+1}` chosen independently) iff
`aᵢᵀx − ρ√(‖x‖₂² + 1) ≥ bᵢ` for every `i` (the constraints of (23)). -/
theorem theorem_5_2 {m K : ℕ} (a : Fin K → Fin m → ℝ) (b : Fin K → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (x : Fin m → ℝ) :
    (∀ i : Fin K, ∀ δa : Fin m → ℝ, ∀ δb : ℝ, ∑ j, δa j ^ 2 + δb ^ 2 ≤ ρ ^ 2 →
        (a i + δa) ⬝ᵥ x ≥ b i + δb) ↔
      ∀ i : Fin K, a i ⬝ᵥ x - ρ * Real.sqrt (∑ j, x j ^ 2 + 1) ≥ b i := by sorry

end RobustSDP.Unstructured
