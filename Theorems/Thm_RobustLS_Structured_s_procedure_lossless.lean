import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

/-- **Lemma 2.1 (S-procedure), converse for p = 1** — El Ghaoui & Lebret (1997), §2.2,
p. 1038 (PDF p. 4). Let `F₀(ζ) = ζᵀT₀ζ + 2u₀ᵀζ + v₀` and `F₁(ζ) = ζᵀT₁ζ + 2u₁ᵀζ + v₁`, with
`T₀ = T₀ᵀ`, `T₁ = T₁ᵀ`, and suppose some `ζ₀` has `F₁(ζ₀) > 0`. If `F₀(ζ) ≥ 0` for every
`ζ` with `F₁(ζ) ≥ 0`, then there is `τ₁ ≥ 0` with `[T₀ u₀; u₀ᵀ v₀] − τ₁ [T₁ u₁; u₁ᵀ v₁] ⪰ 0`. -/
theorem s_procedure_lossless {m : ℕ} (T0 : Matrix (Fin m) (Fin m) ℝ) (u0 : Fin m → ℝ)
    (v0 : ℝ) (T1 : Matrix (Fin m) (Fin m) ℝ) (u1 : Fin m → ℝ) (v1 : ℝ)
    (hT0 : T0ᵀ = T0) (hT1 : T1ᵀ = T1)
    (hslater : ∃ ζ0 : Fin m → ℝ, 0 < quadFn T1 u1 v1 ζ0)
    (himp : ∀ ζ : Fin m → ℝ, 0 ≤ quadFn T1 u1 v1 ζ → 0 ≤ quadFn T0 u0 v0 ζ) :
    ∃ τ1 : ℝ, 0 ≤ τ1 ∧ (quadBlockMat T0 u0 v0 - τ1 • quadBlockMat T1 u1 v1).PosSemidef := by sorry

end RobustLS.Structured
