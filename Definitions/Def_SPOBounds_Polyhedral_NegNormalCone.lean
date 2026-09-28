import Mathlib

namespace SPOBounds.Polyhedral

/-- The negative normal cone `−N_S(x̄) = {ĉ : ĉᵀ(x − x̄) ≥ 0 for all x ∈ S}`
(arXiv:1905.11488v3, §5.2, p. 24, eq. (9), where `𝒦_j := −N_S(v_j)`): the cost vectors for which
`x̄` is an optimal solution of `min_{x ∈ S} ĉᵀx`. Cost vectors are continuous linear functionals,
so `ĉᵀx` is `ĉ x`. -/
def negNormalCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (xbar : E) : Set (StrongDual ℝ E) :=
  {chat | ∀ x ∈ S, 0 ≤ chat (x - xbar)}

end SPOBounds.Polyhedral
