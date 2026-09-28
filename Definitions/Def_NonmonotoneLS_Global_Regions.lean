import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Global_Run

open scoped ENNReal NNReal

namespace NonmonotoneLS.Global

variable {n : ℕ}

/-- The level set `𝓛 = {y : f(y) ≤ f(x₀)}` (Theorem 2.2). -/
def levelSet (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | f y ≤ f x₀}

/-- `d_max = sup_k ‖d_k‖`, taken in `[0, ∞]` (it is `∞` when the directions are unbounded). -/
noncomputable def dmax (d : ℕ → EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ k, (‖d k‖₊ : ℝ≥0∞)

/-- `𝓛̄`: the points whose distance to `𝓛 = {y : f(y) ≤ f(x₀)}` is at most `μ d_max`
(Theorem 2.2), computed in `[0, ∞]`. -/
noncomputable def Lbar (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | Metric.infEDist y (levelSet f (x 0)) ≤ ENNReal.ofReal p.μ * dmax d}

/-- The Lipschitz hypothesis of Theorem 2.2 for the rule `r`, with constant `L`: `∇f` is
`L`-Lipschitz on `𝓛` if the Wolfe conditions are used, and on `𝓛̄` if the Armijo conditions
are used. -/
def LipschitzHyp (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (L : ℝ≥0) : Prop :=
  match r with
  | Rule.wolfe => LipschitzOnWith L (gradient f) (levelSet f (x 0))
  | Rule.armijo => LipschitzOnWith L (gradient f) (Lbar p f x d)

end NonmonotoneLS.Global
