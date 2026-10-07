import Mathlib
import Definitions.Def_TalagrandConc_Assignment_Basic

namespace TalagrandConc.Assignment

/-- Talagrand (1995), p. 167, Corollary 10.2. If the digraph `D_u` of the cost matrix
`X` (entries in `[0, 1]`) is `α`-expanding and `m ≥ 1` is an integer with `α^m ≥ N/2`,
then every optimal assignment `τ` satisfies `X_{i,τ(i)} ≤ 4 m u N⁻¹ log N` for all `i`. -/
theorem corollary_10_2 {N : ℕ} (X : Fin N × Fin N → ℝ) (hX : ∀ p, X p ∈ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : 0 < u) (α : ℝ) (hD : IsExpanding N α (digraphU N u X))
    (m : ℕ) (hm : 1 ≤ m) (hαm : (N : ℝ) / 2 ≤ α ^ m)
    (τ : Equiv.Perm (Fin N)) (hτ : IsOptimalAssignment X τ) (i : Fin N) :
    X (i, τ i) ≤ 4 * m * u * (N : ℝ)⁻¹ * Real.log N := by sorry

end TalagrandConc.Assignment

