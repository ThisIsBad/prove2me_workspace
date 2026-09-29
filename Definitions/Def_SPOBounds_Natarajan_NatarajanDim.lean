import Mathlib

namespace SPOBounds.Natarajan

/-- The class `w*(H) = {x ↦ w*(f(x)) : f ∈ H}` of decisions induced by `H` (p. 11). -/
def oracleClass {X Y Z : Type*} (w : Y → Z) (H : Set (X → Y)) : Set (X → Z) :=
  {g | ∃ f ∈ H, g = fun x => w (f x)}

/-- Definition 1 (p. 10): `F` N-shatters the finite set `T` if there are `g₁, g₂` with
`g₁ x ≠ g₂ x` for every `x ∈ T` such that for every `U ⊆ T` some `g ∈ F` agrees with `g₁` on
`U` and with `g₂` on `T \ U`. The Natarajan dimension is the maximal size of an N-shattered set;
it is not defined as a number here: statements carry an upper bound `k` on the sizes of all
N-shattered sets instead. -/
def NShatters {X Z : Type*} (F : Set (X → Z)) (T : Finset X) : Prop :=
  ∃ g₁ g₂ : X → Z, (∀ x ∈ T, g₁ x ≠ g₂ x) ∧
    ∀ U ⊆ T, ∃ g ∈ F, (∀ x ∈ U, g x = g₁ x) ∧ ∀ x ∈ T, x ∉ U → g x = g₂ x

/-- The set `𝔉_{|𝕏} = {(w*(f(x₁)), …, w*(f(xₙ))) : f ∈ H}` of decision vectors that `w*(H)`
induces on the features of the sample `s` (p. 31). -/
def sampleDecisions {X Y Z C : Type*} {n : ℕ} (w : Y → Z) (H : Set (X → Y))
    (s : Fin n → X × C) : Set (Fin n → Z) :=
  {v | ∃ f ∈ H, v = fun i => w (f (s i).1)}

end SPOBounds.Natarajan
