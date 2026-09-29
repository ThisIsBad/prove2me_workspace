import Mathlib

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Theorem (2.1): the max function `f(x) = max {g(x, u) : u ∈ U}`, written as
the supremum `⨆ u, g x u` (under the hypotheses of Theorem (2.1) it is attained). -/
noncomputable def maxFunction {n : ℕ} {U : Type*} (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ u, g x u

/-- Clarke (1975), Theorem (2.1)(3): `M(x) = {u ∈ U : g(x, u) = f(x)}`, the set of maximizers. -/
def maximizers {n : ℕ} {U : Type*} (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set U :=
  {u | g x u = maxFunction g x}

end ClarkeGradients.MaxFunctions
