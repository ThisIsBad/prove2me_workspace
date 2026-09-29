import Mathlib

namespace RobustMDP.Shared

/-- The support function of a set `S ⊆ ℝⁿ` (Nilim–El Ghaoui 2005, Notation, p. 780):
`σ_S(v) := sup {pᵀ v : p ∈ S}`, written as the real `sSup` of the image of `S` under
`p ↦ ∑ⱼ p j * v j`. On `ℝ`, `sSup` of an empty or unbounded-above set is `0`; every use in this
mission takes `S` nonempty and contained in the probability simplex, where the image is nonempty
and bounded above by `maxⱼ v j`, so `sSup` is the genuine supremum. -/
noncomputable def supportFunction {n : ℕ} (S : Set (Fin n → ℝ)) (v : Fin n → ℝ) : ℝ :=
  sSup ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' S)

end RobustMDP.Shared
