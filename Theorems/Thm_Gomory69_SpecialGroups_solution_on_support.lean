import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- Proof of THEOREM 23 (Gomory 1969, p. 506), corrected: if every nonzero element of `𝒢` has
order `p ∈ {2, 3}` and `t` is an irreducible solution of the group equation, then every solution
`u` vanishing wherever `t` vanishes satisfies `u(g) ≡ t(g) (mod p)` and `u(g) ≥ t(g)` for every
`g`; in particular `t` is the only such solution with all components below `p`. (The page asserts
that `t` is the only such solution outright, which fails, e.g. `𝒢 = ℤ₂`, `t = (1)`, `u = (3)`.) -/
theorem solution_on_support {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t)
    (u : {g : G // g ≠ 0} → ℕ) (hu : u ∈ solutionSet g₀) (hsupp : ∀ g, t g = 0 → u g = 0) :
    ∀ g, u g ≡ t g [MOD p] ∧ t g ≤ u g := by sorry

end Gomory69.SpecialGroups

