import Mathlib

namespace RobustPower.StochGap

/-- Definition 1.1 (p. 5): `H ⊆ ℝⁿ` is a hypercube if `H = {x | lᵢ ≤ xᵢ ≤ uᵢ ∀ i}` for some
`l ≤ u`. -/
def IsHypercube {n : ℕ} (H : Set (Fin n → ℝ)) : Prop :=
  ∃ l u : Fin n → ℝ, l ≤ u ∧ H = Set.Icc l u

/-- Definition 1.2 (p. 5), with a named point of symmetry: `u` belongs to `P` and, for every
`z`, `u + z ∈ P ↔ u - z ∈ P` (display (1.7)). -/
def IsSymmetricAbout {E : Type*} [AddCommGroup E] (P : Set E) (u : E) : Prop :=
  u ∈ P ∧ ∀ z : E, u + z ∈ P ↔ u - z ∈ P

/-- Definition 1.2 (p. 5): `P` is symmetric if it is symmetric about some point `u⁰ ∈ P`. -/
def IsSymmetric {E : Type*} [AddCommGroup E] (P : Set E) : Prop :=
  ∃ u : E, IsSymmetricAbout P u

/-- Definition 1.3 (p. 6): a convex set `P ⊆ ℝⁿ₊` is positive if there is a convex symmetric
set `S ⊆ ℝⁿ₊` with `P ⊆ S` whose point of symmetry lies in `P`. -/
def IsPositive {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  Convex ℝ P ∧ (∀ x ∈ P, 0 ≤ x) ∧
    ∃ S : Set (Fin n → ℝ), Convex ℝ S ∧ (∀ x ∈ S, 0 ≤ x) ∧ P ⊆ S ∧
      ∃ u : Fin n → ℝ, IsSymmetricAbout S u ∧ u ∈ P

/-- Display (2.5) (p. 12): `xʰⱼ`, the largest `j`-th coordinate of a point of `S`
(a supremum; it is a maximum when attained). Meaningful for nonempty bounded `S`. -/
noncomputable def xh {n : ℕ} (S : Set (Fin n → ℝ)) : Fin n → ℝ :=
  fun j => sSup ((fun x : Fin n → ℝ => x j) '' S)

/-- Display (2.6) (p. 12): `xˡⱼ`, the smallest `j`-th coordinate of a point of `S`
(an infimum; it is a minimum when attained). Meaningful for nonempty bounded `S`. -/
noncomputable def xl {n : ℕ} (S : Set (Fin n → ℝ)) : Fin n → ℝ :=
  fun j => sInf ((fun x : Fin n → ℝ => x j) '' S)

/-- Display (2.7) (p. 12): the hypercube `H = {x | xˡⱼ ≤ xⱼ ≤ xʰⱼ ∀ j}`. -/
noncomputable def boundingBox {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  Set.Icc (xl S) (xh S)

end RobustPower.StochGap
