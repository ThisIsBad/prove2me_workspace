import Mathlib

namespace Gomory69.Asymptotic

/-! Gomory (1969), pp. 457–459: the group equation (5), its solution set `T`, the polyhedron
`P(𝒢, 𝒩, g₀)` and irreducible integer points, for an arbitrary Abelian group `𝒢`
(written additively) and a finite set `𝒩` of group elements. -/

variable {G : Type*} [AddCommGroup G]

/-- The nonnegative integer solutions `t = (t(g))_{g ∈ 𝒩}` of the group equation (5),
`∑_{g ∈ 𝒩} t(g) · g = g₀` (p. 457). -/
def groupSolutions (𝒩 : Finset G) (g₀ : G) : Set (↥𝒩 → ℕ) :=
  {t | ∑ g : ↥𝒩, t g • (g : G) = g₀}

/-- The real point of `𝒩`-space with the same coordinates as the integer vector `t`. -/
def toReal (𝒩 : Finset G) (t : ↥𝒩 → ℕ) : ↥𝒩 → ℝ := fun g => (t g : ℝ)

/-- `P(𝒢, 𝒩, g₀)` (pp. 457–458): the convex hull, in the real `n′`-dimensional `T`-space
`↥𝒩 → ℝ`, of the nonnegative integer solutions of the group equation (5). -/
def groupPolyhedron (𝒩 : Finset G) (g₀ : G) : Set (↥𝒩 → ℝ) :=
  convexHull ℝ (toReal 𝒩 '' groupSolutions 𝒩 g₀)

/-- Irreducibility (p. 459): a nonnegative integer vector `t` is irreducible if for all
integer vectors `s, r` with `0 ≤ s(g) ≤ t(g)`, `0 ≤ r(g) ≤ t(g)` and
`∑ s(g) · g = ∑ r(g) · g` one has `r = s`. -/
def IsIrreducible (𝒩 : Finset G) (t : ↥𝒩 → ℕ) : Prop :=
  ∀ s r : ↥𝒩 → ℤ, (∀ g, 0 ≤ s g ∧ s g ≤ (t g : ℤ)) → (∀ g, 0 ≤ r g ∧ r g ≤ (t g : ℤ)) →
    ∑ g : ↥𝒩, s g • (g : G) = ∑ g : ↥𝒩, r g • (g : G) → r = s

end Gomory69.Asymptotic
