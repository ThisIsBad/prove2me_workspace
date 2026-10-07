import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- Proof of THEOREM 23 (Gomory 1969, pp. 505–506): if every nonzero element of `𝒢` has order
`p ∈ {2, 3}`, then for an irreducible solution `t` of the group equation the elements `g` with
`t(g) > 0` form an independent set. -/
theorem irreducible_support_independent {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t) :
    IsIndependent (support t) := by sorry

end Gomory69.SpecialGroups

