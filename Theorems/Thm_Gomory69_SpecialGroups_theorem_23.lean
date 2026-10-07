import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- THEOREM 23 (Gomory 1969, p. 505): if every nonzero element of `𝒢` has order 2, or every
nonzero element has order 3, and `g₀ ≠ 0̄`, then a solution `t` of the group equation is
irreducible if and only if it is a vertex of `P(𝒢, g₀)`; furthermore, the elements `g` with
`t(g) > 0` in such a vertex form an independent set. -/
theorem theorem_23 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (hg₀ : g₀ ≠ 0) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) :
    (IsIrreducible t ↔ toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) ∧
    (toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀) → IsIndependent (support t)) := by sorry

end Gomory69.SpecialGroups

