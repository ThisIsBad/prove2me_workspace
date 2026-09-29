import Mathlib

namespace AKSSorting.Core

/-!
Levels of the tree `T` of finite 0-1 sequences (Ajtai–Komlós–Szemerédi 1983, pp. 2–3).
The level of sequences of length `i` is encoded as `Fin (2 ^ i)`: the sequence
`⟨a₁, …, aᵢ⟩` is the number with binary digits `a₁ … aᵢ` (`a₁` most significant). Numeric order
on `Fin (2 ^ i)` is then the lexicographic order of the paper, appending the bit `b` to `t` gives
`2t + b`, and a sequence `u` of length `i` extends `t` of length `k ≤ i` (`u ≺ t`) iff
`u / 2 ^ (i - k) = t`.
-/

variable {R : Type} [DecidableEq R]

/-- `C` is a chain on level `i` (p. 3): `C(x) ⊆ ℛ` for every node `x` of the level, distinct
nodes carry disjoint sets, and all `C(x)` have the same cardinality. -/
def IsChain {i : ℕ} (C : Fin (2 ^ i) → Finset R) : Prop :=
  (∀ x y, x ≠ y → Disjoint (C x) (C y)) ∧ ∀ x y, (C x).card = (C y).card

/-- `N(C) = |C(x)|` for some (all) `x ∈ Dom(C)`; evaluated at the first node. -/
def chainN {i : ℕ} (C : Fin (2 ^ i) → Finset R) : ℕ :=
  (C ⟨0, Nat.two_pow_pos i⟩).card

/-- `∪C = ⋃_{t ∈ Dom(C)} C(t)`. -/
def chainUnion {i : ℕ} (C : Fin (2 ^ i) → Finset R) : Finset R :=
  Finset.univ.biUnion C

/-- For a chain `C` on level `i` and a node `t'` on level `k ≤ i`:
`⋃_{l(t) = i, t ≺ t'} C(t)`, the union of `C` over the level-`i` descendants of `t'`. -/
def subtreeUnion {i : ℕ} (C : Fin (2 ^ i) → Finset R) (k : ℕ) (t' : Fin (2 ^ k)) : Finset R :=
  (Finset.univ.filter fun u : Fin (2 ^ i) => u.val / 2 ^ (i - k) = t'.val).biUnion C

end AKSSorting.Core
