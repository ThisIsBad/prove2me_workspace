import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

namespace HunterPDE.Regularity

/-- Proposition 4.52 (1) of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 124 (commutativity of
difference quotients with weak derivatives): if `u, ∂ᵢu ∈ L¹_loc(ℝⁿ)`, then
`∂ᵢ D_j^h u = D_j^h ∂ᵢ u`. Here `g` is a weak `i`th partial derivative of `u` on `ℝⁿ`
(`HasWeakDeriv Set.univ (Pi.single i 1) u g`, which includes `u, g ∈ L¹_loc(ℝⁿ)`), and the
conclusion is that `D_j^h g` is a weak `i`th partial derivative of `D_j^h u` on `ℝⁿ`. The size
`h` is nonzero as in Definition 4.51. Coordinates are 0-based. -/
theorem weakDeriv_diffQuot_comm {n : ℕ} (i j : Fin n) (h : ℝ) (hh : h ≠ 0)
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Shared.HasWeakDeriv Set.univ (Pi.single i 1) u g) :
    Shared.HasWeakDeriv Set.univ (Pi.single i 1) (diffQuot j h u) (diffQuot j h g) := by sorry

end HunterPDE.Regularity
