import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction

namespace TeschlODE.Stability

/-- Teschl, §6.6, p. 201: a strict Liapunov function is a Liapunov function for which
equality in (6.36) never occurs: for every solution `φ` on an open interval `J` and all
`t₀ < t₁` in `J` with `φ t₀, φ t₁ ∈ U \ {x₀}` we have `L (φ t₁) < L (φ t₀)`. -/
def IsStrictLiapunovFunction {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsLiapunovFunction f M x₀ U L ∧
  ∀ (J : Set ℝ) (φ : ℝ → EuclideanSpace ℝ (Fin n)), IsIntegralCurve f M J φ →
    ∀ t₀ ∈ J, ∀ t₁ ∈ J, t₀ < t₁ → φ t₀ ∈ U \ {x₀} → φ t₁ ∈ U \ {x₀} →
      L (φ t₁) < L (φ t₀)

end TeschlODE.Stability
