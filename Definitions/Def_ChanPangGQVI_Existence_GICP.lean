import Mathlib

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 212, §2: the dual cone of a set `S ⊆ ℝⁿ`,
`S* = {y ∈ ℝⁿ : yᵀ x ≥ 0 for all x ∈ S}`. -/
def dualConeSet {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ S, 0 ≤ ⟪y, x⟫}

/-- Chan and Pang 1982, p. 212, equation (1): for a point-to-point mapping `m` and a
cone-valued mapping `L` of `ℝⁿ`, `K(x) = m(x) + L(x) = {x' : x' = m(x) + y for some y ∈ L(x)}`.
Cones are convex and contain the origin (footnote 1, p. 212), hence `PointedCone ℝ _`. -/
def coneTranslate {n : ℕ} (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) → PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x' | ∃ z ∈ L x, x' = m x + z}

/-- Chan and Pang 1982, p. 213, §2: a solution of the generalized implicit complementarity
problem `GICP(L, m, f)` is a pair `(x, y)` with `x ∈ m(x) + L(x)`, `y ∈ f(x) ∩ L(x)*` and
`yᵀ (x - m(x)) = 0`. -/
def IsGICPSolution {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → PointedCone ℝ (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ coneTranslate m L x ∧ y ∈ f x ∧ y ∈ dualConeSet (L x : Set (EuclideanSpace ℝ (Fin n))) ∧
    ⟪y, x - m x⟫ = 0

end ChanPangGQVI.Existence
