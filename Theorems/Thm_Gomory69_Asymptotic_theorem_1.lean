import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron

namespace Gomory69.Asymptotic

/-- THEOREM 1 (p. 459): an irreducible nonnegative integer vector `t` on a set `𝒩` of
nonzero elements of a finite Abelian group `𝒢` satisfies `∏_{g ∈ 𝒩} (1 + t(g)) ≤ |𝒢|`. -/
theorem theorem_1 {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∏ g : ↥𝒩, (1 + t g) ≤ Fintype.card G := by sorry

end Gomory69.Asymptotic

