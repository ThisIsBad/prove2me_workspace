import Mathlib

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The empirical distribution of `N` training samples `ξ̂ : Fin N → ℝ^m`, Kuhn et al. 2019,
Example 1(1), p. 2: `PN = (1/N) Σ_{i=1}^N δ_{ξ̂ i}`. Redefined locally in this chapter's own
namespace; see `Def_WassersteinDRO_Guarantees_meanVector` for why. -/
noncomputable def empiricalDistribution {m N : ℕ} (ξhat : Fin N → EuclideanSpace ℝ (Fin m)) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (ξhat i)

end WassersteinDRO.Guarantees
