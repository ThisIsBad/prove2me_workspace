import Mathlib
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace GoldenRatioVI.Fixed

/-- The averaging step of (6): for every `k ≥ 1`,
`z̄ᵏ = ((φ - 1) zᵏ + z̄ᵏ⁻¹) / φ` with `φ = (√5 + 1)/2` the golden ratio. -/
def IsGoldenAveraging {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z zbar : ℕ → E) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    zbar k = Real.goldenRatio⁻¹ • ((Real.goldenRatio - 1) • z k + zbar (k - 1))

/-- A run of the Golden Ratio Algorithm (6) with fixed step `lam`, started from arbitrary
`z¹, z̄⁰` (the entry `z 0` is unused): for every `k ≥ 1`,
`z̄ᵏ = ((φ - 1) zᵏ + z̄ᵏ⁻¹) / φ` and `zᵏ⁺¹ = prox_{λ g}(z̄ᵏ - λ F(zᵏ))`, the latter as the
argmin predicate `IsProxPoint` for the function `x ↦ λ · g x`. -/
def IsGRAALRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) (F : E → E) (lam : ℝ) (z zbar : ℕ → E) : Prop :=
  IsGoldenAveraging z zbar ∧
    ∀ k : ℕ, 1 ≤ k →
      GoldenRatioVI.Shared.IsProxPoint (fun x => (lam : EReal) * g x) (zbar k - lam • F (z k)) (z (k + 1))

end GoldenRatioVI.Fixed
