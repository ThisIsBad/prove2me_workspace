import Mathlib

namespace AppliedComb.Posets

open Classical in
/-- Width of a finite poset (Keller & Trotter, *Applied Combinatorics*, 2017 Edition, p. 119):
the largest `w` for which there exists an antichain of `w` points. An antichain is a subset
in which every distinct pair of points is incomparable (Mathlib's `IsAntichain (· ≤ ·)`);
the empty set is an antichain, so the maximum is taken over a nonempty finite family. -/
noncomputable def width (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  ((Finset.univ : Finset (Finset α)).filter
    (fun A : Finset α => IsAntichain (· ≤ ·) (A : Set α))).sup Finset.card

open Classical in
/-- Height of a finite poset (Keller & Trotter, p. 119): the largest `h` for which there exists
a chain of `h` points. A chain is a subset in which every distinct pair of points is comparable
(Mathlib's `IsChain (· ≤ ·)`); the empty set is a chain. -/
noncomputable def height (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  ((Finset.univ : Finset (Finset α)).filter
    (fun C : Finset α => IsChain (· ≤ ·) (C : Set α))).sup Finset.card

end AppliedComb.Posets
