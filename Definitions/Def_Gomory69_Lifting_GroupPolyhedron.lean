import Mathlib

namespace Gomory69.Lifting

/-- `𝒢⁺ = 𝒢 − 0̄`, the nonzero elements of the group; the coordinates of T-space for
`P(𝒢, g₀) = P(𝒢, 𝒢⁺, g₀)`. -/
abbrev Plus (G : Type*) [AddCommGroup G] : Type _ := {g : G // g ≠ 0}

/-- The set `T` of nonnegative integer solutions of the group equation (5),
`∑_{g ∈ 𝒢⁺} t(g) · g = g₀`. The zero solution is excluded, as stipulated for
`g₀ = 0̄` in the footnote on p. 474; for `g₀ ≠ 0̄` this exclusion is automatic. -/
def T (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (g₀ : G) :
    Set (Plus G → ℕ) :=
  {t | (∑ g : Plus G, t g • (g : G) = g₀) ∧ t ≠ 0}

/-- A nonnegative integer vector viewed as a point of real T-space. -/
def castVec {G : Type*} [AddCommGroup G] (t : Plus G → ℕ) : Plus G → ℝ :=
  fun g => (t g : ℝ)

/-- The master polyhedron `P(𝒢, g₀)`: the convex hull of `T` in real T-space. -/
def P (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (g₀ : G) :
    Set (Plus G → ℝ) :=
  convexHull ℝ (castVec '' T G g₀)

/-- `(π, π₀)` is a face (facet) of `P(𝒢, g₀)`: `π ≠ 0`, (i)′ `π · t ≥ π₀` for every `t ∈ T`,
and (ii)′ the points of `T` on the hyperplane `π · t = π₀` generate it, i.e. their affine span is
the whole hyperplane. -/
def IsFace (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (g₀ : G)
    (π : Plus G → ℝ) (π₀ : ℝ) : Prop :=
  π ≠ 0 ∧ (∀ t ∈ T G g₀, π₀ ≤ π ⬝ᵥ castVec t) ∧
    ((affineSpan ℝ (castVec '' {t | t ∈ T G g₀ ∧ π ⬝ᵥ castVec t = π₀}) : Set (Plus G → ℝ)) =
      {x | π ⬝ᵥ x = π₀})

/-- Extension of a coefficient vector on `𝒢⁺` to all of `𝒢` by the convention `π(0̄) = 0`. -/
def ext {G : Type*} [AddCommGroup G] [DecidableEq G] (π : Plus G → ℝ) : G → ℝ :=
  fun g => if hg : g = 0 then 0 else π ⟨g, hg⟩

end Gomory69.Lifting
