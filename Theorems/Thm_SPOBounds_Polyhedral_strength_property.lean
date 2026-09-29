import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy

namespace SPOBounds.Polyhedral

/-- Theorem 8, strength claim, arXiv:1905.11488v3, p. 25: if `S = conv{v_1, …, v_K}` (distinct
`v_i`) is not a singleton, then for every optimization oracle `w*` the strength property (5)
holds with parameter `μ = 2 / Δ(S)`, where `Δ(S)` is the diameter of `S`; the parameter is
positive, as Definition 3 requires. -/
theorem strength_property {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ} (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ x ∈ S, c (w c) ≤ c x) :
    0 < 2 / Metric.diam S ∧ SPOBounds.Shared.StrengthProperty S (2 / Metric.diam S) w := by sorry

end SPOBounds.Polyhedral

