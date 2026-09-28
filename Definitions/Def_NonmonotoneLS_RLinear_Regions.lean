import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params

open scoped ENNReal NNReal InnerProductSpace

namespace NonmonotoneLS.RLinear

variable {n : ℕ}

/-- The level set `𝓛 = {y : f(y) ≤ f(x₀)}` (p. 1050). -/
def levelSet (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | f y ≤ f x₀}

/-- `d_max = sup_k ‖d_k‖`, taken in `[0, ∞]` (it is `∞` when the directions are unbounded). -/
noncomputable def dmax (d : ℕ → EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ k, (‖d k‖₊ : ℝ≥0∞)

/-- `𝓛̄`: the points whose distance to `𝓛 = {y : f(y) ≤ f(x₀)}` is at most `μ d_max`
(p. 1050), computed in `[0, ∞]`. -/
noncomputable def Lbar (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | Metric.infEDist y (levelSet f (x 0)) ≤ ENNReal.ofReal p.μ * dmax d}

/-- Strong convexity in the form (3.1) (p. 1049), with the paper's constant `γ > 0`
(the modulus is `1/γ`): `f(x) ≥ f(y) + ∇f(y)(x - y) + (1/(2γ)) ‖x - y‖²` for all `x, y`. -/
def IsStronglyConvexWith (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ : ℝ) : Prop :=
  0 < γ ∧ ∀ x y : EuclideanSpace ℝ (Fin n),
    f y + ⟪gradient f y, x - y⟫_ℝ + 1 / (2 * γ) * ‖x - y‖ ^ 2 ≤ f x

end NonmonotoneLS.RLinear
