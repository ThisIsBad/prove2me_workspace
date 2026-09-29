import Mathlib

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The empirical distribution of `N` training samples `ξ̂ : Fin N → E`, Kuhn et al. 2019,
Example 1(1), p. 2: `PN = (1/N) Σ_{i=1}^N δ_{ξ̂ i}`, the uniform mixture of Dirac masses at
the samples. -/
noncomputable def empiricalDistribution {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξhat : Fin N → E) : Measure E :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (ξhat i)

end WassersteinDRO.Duality
