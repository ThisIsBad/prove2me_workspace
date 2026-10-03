import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve

namespace TeschlODE.Stability

/-- Teschl, §6.6, pp. 200–201, (6.35)–(6.36): `L` is a Liapunov function for `ẋ = f(x)` at
`x₀` on the open neighborhood `U` of `x₀` (with `U ⊆ M`): `L` is continuous on `U`, zero at
`x₀`, positive on `U \ {x₀}`, and for every solution `φ` (integral curve on an open interval
`J`) and all `t₀ < t₁` in `J` with `φ t₀, φ t₁ ∈ U \ {x₀}` we have `L (φ t₀) ≥ L (φ t₁)`.
Only the values of `L` on `U` matter. -/
def IsLiapunovFunction {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsOpen U ∧ x₀ ∈ U ∧ U ⊆ M ∧ ContinuousOn L U ∧ L x₀ = 0 ∧
  (∀ x ∈ U, x ≠ x₀ → 0 < L x) ∧
  ∀ (J : Set ℝ) (φ : ℝ → EuclideanSpace ℝ (Fin n)), IsIntegralCurve f M J φ →
    ∀ t₀ ∈ J, ∀ t₁ ∈ J, t₀ < t₁ → φ t₀ ∈ U \ {x₀} → φ t₁ ∈ U \ {x₀} →
      L (φ t₁) ≤ L (φ t₀)

end TeschlODE.Stability
