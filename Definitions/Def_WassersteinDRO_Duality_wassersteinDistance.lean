import Mathlib

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The type-`p` Wasserstein distance between two Borel probability measures `Q`, `Q'` on `E`
(representing `ℝ^m` with an arbitrary fixed norm), Kuhn–Mohajerin Esfahani–Nguyen–
Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization*, INFORMS TutORials
2019, Definition 1, p. 3, eq. (5):

`Wp(Q,Q') = (inf_{π ∈ Π(Q,Q')} ∫ ‖ξ-ξ'‖^p π(dξ,dξ'))^{1/p}`,

where `Π(Q,Q')` is the set of couplings of `Q` and `Q'`: joint measures on `E × E` whose two
marginals (pushforwards under the coordinate projections) are `Q` and `Q'`. The infimum over
the constrained set of couplings is encoded as an infimum guarded by the coupling condition,
which defaults to `⊤` outside the feasible set — the standard Mathlib idiom for a constrained
extremum, not a junk value, since it correctly represents "no such π" as "no finite cost". -/
noncomputable def wassersteinDistance {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (p : ℝ) (Q Q' : Measure E) : ENNReal :=
  (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'),
      ∫⁻ x : E × E, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) ^ (1 / p)

end WassersteinDRO.Duality
