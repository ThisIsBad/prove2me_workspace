import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The Wasserstein ambiguity set, Kuhn et al. 2019, p. 6, displayed equation just before
eq. (6): `Bε,p(PN) = {Q ∈ P(Ξ) : Wp(Q,PN) ≤ ε}`, the ball of radius `ε ≥ 0` around the
nominal distribution `PN` in the type-`p` Wasserstein distance, restricted to probability
measures supported on the closed set `Ξ`. "Supported on `Ξ`" is encoded as `Q Ξᶜ = 0`
(the complement is `Q`-null), the standard measure-theoretic reading of `Q ∈ P(Ξ)`. -/
def ambiguitySet {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) : Set (Measure E) :=
  {Q | Q Set.univ = 1 ∧ Q Ξᶜ = 0 ∧ wassersteinDistance p Q PN ≤ ENNReal.ofReal ε}

end WassersteinDRO.Duality
