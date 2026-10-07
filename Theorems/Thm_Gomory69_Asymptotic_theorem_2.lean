import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron

namespace Gomory69.Asymptotic

/-- THEOREM 2 (p. 460): every vertex of `P(𝒢, 𝒩, g₀)` is (the real image of) an
irreducible nonnegative integer solution of the group equation (5). -/
theorem theorem_2 {G : Type*} [AddCommGroup G] [Finite G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (g₀ : G) (v : ↥𝒩 → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (groupPolyhedron 𝒩 g₀)) :
    ∃ t ∈ groupSolutions 𝒩 g₀, toReal 𝒩 t = v ∧ IsIrreducible 𝒩 t := by sorry

end Gomory69.Asymptotic

