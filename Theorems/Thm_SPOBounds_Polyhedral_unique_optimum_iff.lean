import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_Polyhedral_NegNormalCone

namespace SPOBounds.Polyhedral

/-- Proposition 2, arXiv:1905.11488v3, p. 25: for `S = conv{v_1, …, v_K}` (distinct `v_i`,
`K ≥ 1`), `P(ĉ)` has a unique optimal solution iff `ĉ ∈ int(𝒦_j)` for some `j`, and
consequently `𝒞° = ℝ^d ∖ ⋃_j int(𝒦_j)`. Interiors are taken in the norm topology of the dual
space `StrongDual ℝ E`. -/
theorem unique_optimum_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ} (hK : 0 < K) (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) :
    (∀ chat : StrongDual ℝ E,
      (∃! u, u ∈ S ∧ IsMinOn (fun x => chat x) S u) ↔
        ∃ j, chat ∈ interior (negNormalCone S (v j))) ∧
    SPOBounds.Shared.degenerate S = (⋃ j, interior (negNormalCone S (v j)))ᶜ := by sorry

end SPOBounds.Polyhedral

