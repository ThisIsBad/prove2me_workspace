import Mathlib
import Definitions.Def_FracPackCover_General_Improve

namespace FracPackCover.General

/-- Theorem 4.4 (p. 27), for IMPROVE-GENERAL with the corrected parameters
`α = 4λ₀⁻¹ ln(12mρλ₀⁻¹)`, `σ = λ₀/(48αρ²)`. Started at `x₀ ∈ P` with `λ₀ = λ(x₀) > 0`, every
exact minimizing oracle, the procedure stops (its loop test fails) within
`B = 2 + 8640 ρ² λ₀⁻² ln(12mρλ₀⁻¹)` loop tests and makes at most `B` oracle calls (the paper writes
`O(ρ²λ₀⁻² log(mρλ₀⁻¹))` iterations). -/
theorem theorem_4_4 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMinOracle P A orc)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ P) (hlam : 0 < lam A b d x0) (fuel : ℕ)
    (hfuel : 2 + 8640 * ρ ^ 2 / lam A b d x0 ^ 2 * Real.log (12 * m * ρ / lam A b d x0)
      ≤ (fuel : ℝ)) :
    (improveGeneral A b d ρ orc fuel x0).exit ≠ ImproveExit.outOfFuel ∧
      ((improveGeneral A b d ρ orc fuel x0).calls : ℝ) ≤
        2 + 8640 * ρ ^ 2 / lam A b d x0 ^ 2 * Real.log (12 * m * ρ / lam A b d x0) := by sorry

end FracPackCover.General

