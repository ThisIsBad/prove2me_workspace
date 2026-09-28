import Mathlib
import Definitions.Def_SPOBounds_Polyhedral_NegNormalCone

namespace SPOBounds.Polyhedral

/-- arXiv:1905.11488v3, §5.2, p. 24, eq. (9): for `S = conv{v_1, …, v_K}` with distinct `v_i`,
`𝒦_j = −N_S(v_j) = {ĉ : ĉᵀ(v_i − v_j) ≥ 0 for all i = 1, …, K}`. -/
theorem negNormalCone_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℕ} (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (j : Fin K) :
    negNormalCone S (v j) = {chat : StrongDual ℝ E | ∀ i, 0 ≤ chat (v i - v j)} := by sorry

end SPOBounds.Polyhedral
