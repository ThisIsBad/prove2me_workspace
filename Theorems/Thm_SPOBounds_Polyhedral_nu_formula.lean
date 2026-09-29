import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy

namespace SPOBounds.Polyhedral

/-- Theorem 8, eq. (10), arXiv:1905.11488v3, p. 25: if `S = conv{v_1, …, v_K}` (distinct `v_i`)
is not a singleton, then for every optimization oracle `w*` and every cost vector `ĉ`,
`ν_S(ĉ) = min_{j : v_j ≠ w*(ĉ)} ĉᵀ(v_j − w*(ĉ)) / ‖v_j − w*(ĉ)‖`
(the minimum over a nonempty finite index set, stated as `IsLeast`). -/
theorem nu_formula {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ} (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ x ∈ S, c (w c) ≤ c x)
    (chat : StrongDual ℝ E) :
    IsLeast ((fun j => chat (v j - w chat) / ‖v j - w chat‖) '' {j | v j ≠ w chat})
      (SPOBounds.Shared.nu S chat) := by sorry

end SPOBounds.Polyhedral

