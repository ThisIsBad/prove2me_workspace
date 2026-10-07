import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- The vertex characterization of p. 506 (Gomory 1969): if every nonzero element of `𝒢` has order
`s ∈ {2, 3}`, a nonzero nonnegative integer vector `t` is a vertex of `P(𝒢, g₀)` for some
`g₀ ≠ 0̄` if and only if the `g` with `t(g) > 0` are independent and `t(g) < s` for all `g`. -/
theorem vertex_characterization {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : ℕ) (hs : s = 2 ∨ s = 3) (hG : AllNonzeroOfOrder G s)
    (t : {g : G // g ≠ 0} → ℕ) (ht : t ≠ 0) :
    (∃ g₀ : G, g₀ ≠ 0 ∧ t ∈ solutionSet g₀ ∧ toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀)) ↔
      (IsIndependent (support t) ∧ ∀ g, t g < s) := by sorry

end Gomory69.SpecialGroups

