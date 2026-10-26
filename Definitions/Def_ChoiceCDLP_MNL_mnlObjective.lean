import Mathlib

namespace ChoiceCDLP.MNL

/-- The objective of the single-segment MNL offer-set problem (14) of Liu and van Ryzin (2008,
Proposition 6, p. 300), written for an offer set `S` of the consideration set `ι` (the paper's
`y_j = 1` iff `j ∈ S`): with preference weights `v j`, no-purchase weight `v₀` and scores `w j`,
`f(S) = (∑_{j ∈ S} w_j v_j) / (∑_{j ∈ S} v_j + v₀)`.
When `S = ∅` and `v₀ = 0` the quotient is `0 / 0 = 0` in Lean, the paper's convention
`h(0) := 0` (p. 309). -/
noncomputable def mnlObjective {ι : Type*} (v w : ι → ℝ) (v₀ : ℝ) (S : Finset ι) : ℝ :=
  (∑ j ∈ S, w j * v j) / (∑ j ∈ S, v j + v₀)

end ChoiceCDLP.MNL
