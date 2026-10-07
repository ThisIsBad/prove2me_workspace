import Mathlib

namespace ShapleyScarf.Balanced

def coordinateSlice {N : Type*} [Fintype N] (S : Finset N) : Set (N → ℝ) :=
  {x | ∀ j, j ∉ S → x j = 0}

def singletonInteriorUnion {N : Type*} [Fintype N] [DecidableEq N]
    (V : Finset N → Set (N → ℝ)) (S : Finset N) : Set (N → ℝ) :=
  ⋃ i ∈ (S : Set N), interior (V {i})

def IsNTUGame {N : Type*} [Fintype N] [DecidableEq N]
    (V : Finset N → Set (N → ℝ)) : Prop :=
  ∀ S : Finset N, S.Nonempty →
    IsClosed (V S) ∧
    (∀ x y : N → ℝ, x ∈ V S → (∀ i ∈ S, y i ≤ x i) → y ∈ V S) ∧
    Bornology.IsBounded ((V S \ singletonInteriorUnion V S) ∩ coordinateSlice S) ∧
    ((V S \ singletonInteriorUnion V S) ∩ coordinateSlice S).Nonempty

end ShapleyScarf.Balanced
