import Mathlib

namespace Disjunctive.Polarity

/-- The polyhedron `Q := {(u,x) : Au + Bx ≤ b}` being projected (Balas §2.2, p. 27; note the
roles of `A`/`B` and the `≤` convention are as in this section, reversed from Chapter 1). -/
def Poly2 {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) : Set ((Fin p → ℝ) × (Fin q → ℝ)) :=
  {ux | A.mulVec ux.1 + B.mulVec ux.2 ≤ b}

/-- The projection `Proj_x(Q) := {x : ∃ u, (u,x) ∈ Q}` onto the `x`-space (Balas §2.2, p. 27). -/
def ProjOntoX {p q : ℕ} (Q : Set ((Fin p → ℝ) × (Fin q → ℝ))) : Set (Fin q → ℝ) :=
  {x | ∃ u : Fin p → ℝ, (u, x) ∈ Q}

/-- The projection cone `W := {v : vA = 0, v ≥ 0}` associated with `Proj_x(Q)` (Balas §2.2,
p. 27). -/
def ProjectionCone {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : Set (Fin m → ℝ) :=
  {v | Matrix.vecMul v A = 0 ∧ 0 ≤ v}

/-- `v` is an extreme ray of a cone `W` in a real vector space `E` (Balas §2.2, p. 27, `extr W`):
`v` is nonzero, belongs to `W`, and the ray it generates is an extreme subset of `W`. -/
def IsExtremeRay {E : Type*} [AddCommGroup E] [Module ℝ E] (W : Set E) (v : E) : Prop :=
  v ≠ 0 ∧ v ∈ W ∧ IsExtreme ℝ W {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • v}

/-- A polyhedron in `ι → ℝ` is **integral** (Balas §2.2, p. 28, Proposition 2.6): it is the
closed convex hull of its own integer points. Integrality read off the *vertices* alone is
vacuous for a polyhedron with a lineality space, which has none: `{(u,x) : 2x = 1}` would be
integral and project onto `{1/2}`, refuting Proposition 2.6. -/
def IsIntegral {ι : Type*} (P : Set (ι → ℝ)) : Prop :=
  P = closure (convexHull ℝ {x ∈ P | ∀ i, ∃ k : ℤ, x i = (k : ℝ)})

/-- A polyhedron `Q ⊆ (Fin p → ℝ) × (Fin q → ℝ)` (the shape of `Poly2`) is integral in the same
sense: the closed convex hull of its points with integer `u`- and `x`-coordinates. -/
def IsIntegralPair {p q : ℕ} (P : Set ((Fin p → ℝ) × (Fin q → ℝ))) : Prop :=
  P = closure (convexHull ℝ
    {ux ∈ P | (∀ i, ∃ k : ℤ, ux.1 i = (k : ℝ)) ∧ ∀ j, ∃ k : ℤ, ux.2 j = (k : ℝ)})

open Classical in
/-- The dimension of a polyhedron `P` in any real vector space `E`: the dimension of the linear
span of its difference set, i.e. of its affine hull (Balas §2.2.2, p. 29, `dim(Q)`). Used both
for `Q ⊆ (Fin p → ℝ) × (Fin q → ℝ)` itself and for its projection `Proj_x(Q) ⊆ Fin q → ℝ`. -/
noncomputable def PolyDim {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : ℤ :=
  if P.Nonempty then (Module.finrank ℝ (vectorSpan ℝ P) : ℤ) else -1

/-- `FQ`, the candidate face of `Q` cut out by the valid inequality `αu + βx ≤ β₀` at equality
(Balas §2.2.3, p. 30). -/
def FacetCandidate {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) (α : Fin p → ℝ) (β : Fin q → ℝ) (β0 : ℝ) :
    Set ((Fin p → ℝ) × (Fin q → ℝ)) :=
  Poly2 A B b ∩ {ux | dotProduct α ux.1 + dotProduct β ux.2 = β0}

/-- `F` is a facet of `Q`: a proper extreme subset (face) of codimension exactly `1` (Balas
§2.2.3, p. 30, used implicitly via "`dim(FQ) = dim(Q) - 1`" for a facet `FQ` of `Q`; stated
generically over any real vector space `E` so it also applies to `cl conv F ⊆ Fin n → ℝ` itself
in Theorem 2.18, not only to `Q ⊆ (Fin p → ℝ) × (Fin q → ℝ)`). -/
def IsFacet {E : Type*} [AddCommGroup E] [Module ℝ E] (Q F : Set E) : Prop :=
  IsExtreme ℝ Q F ∧ F.Nonempty ∧ PolyDim F = PolyDim Q - 1

end Disjunctive.Polarity
