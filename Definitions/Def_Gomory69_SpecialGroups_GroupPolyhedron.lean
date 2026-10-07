import Mathlib

namespace Gomory69.SpecialGroups

/-!
Gomory, *Some polyhedra related to combinatorial problems*, Linear Algebra Appl. 2 (1969):
the group equation (5) and (12) (pp. 457, 475), the master polyhedron `P(𝒢, g₀)` (pp. 474–475,
with the footnote of p. 474), irreducibility (p. 459), independent group elements (p. 504), and the
groups all of whose nonzero elements have one order `p` (p. 504).

The finite Abelian group `𝒢` is written additively. A point of T-space is a vector indexed by
`𝒢⁺ = 𝒢 − 0̄`, the subtype `{g : G // g ≠ 0}`.
-/

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The left-hand side of the group equation (12), p. 475: `Σ_{g ∈ 𝒢⁺} t(g) · g`, for a
nonnegative integer vector `t` indexed by the nonzero group elements. -/
def groupSum (t : {g : G // g ≠ 0} → ℕ) : G :=
  ∑ g, t g • (g : G)

/-- The set of nonnegative integer solutions of the group equation (12),
`Σ_{g ∈ 𝒢⁺} t(g) · g = g₀` (p. 475). For `g₀ = 0̄` the solution `t = 0` is excluded, as in the
footnote of p. 474. -/
def solutionSet (g₀ : G) : Set ({g : G // g ≠ 0} → ℕ) :=
  {t | groupSum t = g₀ ∧ (g₀ = 0 → t ≠ 0)}

/-- A nonnegative integer vector of T-space viewed as a real vector. -/
def toReal (t : {g : G // g ≠ 0} → ℕ) : {g : G // g ≠ 0} → ℝ :=
  fun g => (t g : ℝ)

/-- The master polyhedron `P(𝒢, g₀)` (pp. 474–475): the convex hull, in the real
`(|𝒢| − 1)`-dimensional T-space, of the nonnegative integer solutions of (12). Its vertices are its
extreme points, `Set.extremePoints ℝ (masterPolyhedron g₀)`. -/
def masterPolyhedron (g₀ : G) : Set ({g : G // g ≠ 0} → ℝ) :=
  convexHull ℝ (toReal '' solutionSet g₀)

/-- Irreducibility (p. 459): a nonnegative integer vector `t` is irreducible if for all nonnegative
integer vectors `r, s` with `0 ≤ r ≤ t`, `0 ≤ s ≤ t` (componentwise),
`Σ s(g) · g = Σ r(g) · g` implies `r = s`. -/
def IsIrreducible (t : {g : G // g ≠ 0} → ℕ) : Prop :=
  ∀ r s : {g : G // g ≠ 0} → ℕ, r ≤ t → s ≤ t → groupSum s = groupSum r → r = s

/-- The set of group elements `g` with `t(g) > 0` (called `T` on pp. 505–506). -/
def support (t : {g : G // g ≠ 0} → ℕ) : Finset G :=
  (Finset.univ.filter (fun g => 0 < t g)).map (Function.Embedding.subtype _)

/-- Independent group elements (p. 504): a set `S` of group elements is independent if, for all
integers `s_g`, `Σ_{g ∈ S} s_g g = 0̄` implies `s_g g = 0̄` for every `g ∈ S`. -/
def IsIndependent (S : Finset G) : Prop :=
  ∀ s : G → ℤ, ∑ g ∈ S, s g • g = 0 → ∀ g ∈ S, s g • g = 0

end Gomory69.SpecialGroups

namespace Gomory69.SpecialGroups

/-- The hypothesis of §3F (p. 504) for a fixed `p`: every nonzero element of `𝒢` has order `p`
(the zero element has order `1`). With `p = 2` these are the groups `𝒢₂, 𝒢₂,₂, …`; with `p = 3` the
groups `𝒢₃, 𝒢₃,₃, …`. -/
def AllNonzeroOfOrder (G : Type*) [AddCommGroup G] (p : ℕ) : Prop :=
  ∀ g : G, g ≠ 0 → addOrderOf g = p

end Gomory69.SpecialGroups
