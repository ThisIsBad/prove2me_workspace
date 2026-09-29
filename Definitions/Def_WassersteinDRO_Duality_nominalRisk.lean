import Mathlib

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The nominal risk of a loss function `ℓ` under a distribution `Q`, Kuhn et al. 2019,
implicit throughout Section 1 (e.g. Example 2, p. 3): `R(Q,ℓ) = E_Q[ℓ(ξ)]`, the Bochner
expectation of `ℓ` under `Q`. Every theorem that uses this definition also carries an
`Integrable` hypothesis on `ℓ`, so Mathlib's junk value `0` for a non-integrable integrand
never enters a faithfulness-relevant equation or bound. -/
noncomputable def nominalRisk {E : Type*} [MeasurableSpace E] (Q : Measure E) (ℓ : E → ℝ) : ℝ :=
  ∫ x, ℓ x ∂Q

end WassersteinDRO.Duality
