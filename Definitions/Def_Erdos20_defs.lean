import Mathlib

namespace Erdos20

/-- A family `F` is a sunflower with kernel `S` if any two distinct members of `F`
intersect exactly in `S`. -/
def IsSunflowerWithKernel {α : Type*} (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

/-- A family `F` is a sunflower if all pairwise intersections of distinct members coincide. -/
def IsSunflower {α : Type*} (F : Set (Set α)) : Prop :=
  ∃ S, IsSunflowerWithKernel F S

theorem isSunflower_empty {α : Type*} : IsSunflower (∅ : Set (Set α)) :=
  ⟨∅, by simp [IsSunflowerWithKernel]⟩

theorem isSunflower_singleton {α : Type*} (A : Set α) : IsSunflower {A} :=
  ⟨∅, by simp [IsSunflowerWithKernel]⟩

/-- `f n k` is the least `m` such that every family of `n`-element sets with at least `m`
members contains a `k`-sunflower. -/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

end Erdos20
