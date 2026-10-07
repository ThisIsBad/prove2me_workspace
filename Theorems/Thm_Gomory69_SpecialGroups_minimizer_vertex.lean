import Mathlib
import Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron

namespace Gomory69.SpecialGroups

/-- Proof of THEOREM 23 (Gomory 1969, p. 506), corrected: if every nonzero element of `𝒢` has
order `p ∈ {2, 3}` and `t` is an irreducible solution of the group equation, put `π(g) = 0` where
`t(g) > 0` and `π(g) = 1` where `t(g) = 0`. Then `t` minimizes `π · u` over the solutions `u`,
every minimizer `u` satisfies `u ≥ t` componentwise, and `t` is a vertex of `P(𝒢, g₀)`. -/
theorem minimizer_vertex {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p : ℕ) (hp : p = 2 ∨ p = 3) (hG : AllNonzeroOfOrder G p)
    (g₀ : G) (t : {g : G // g ≠ 0} → ℕ) (ht : t ∈ solutionSet g₀) (hirr : IsIrreducible t) :
    let π : {g : G // g ≠ 0} → ℕ := fun g => if t g = 0 then 1 else 0
    (∀ u ∈ solutionSet g₀, ∑ g, π g * t g ≤ ∑ g, π g * u g) ∧
    (∀ u ∈ solutionSet g₀, ∑ g, π g * u g = ∑ g, π g * t g → t ≤ u) ∧
    toReal t ∈ Set.extremePoints ℝ (masterPolyhedron g₀) := by sorry

end Gomory69.SpecialGroups

