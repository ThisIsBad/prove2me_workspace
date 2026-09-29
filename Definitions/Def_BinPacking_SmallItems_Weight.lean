import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model

namespace BinPacking.SmallItems

open Classical

/-- `x` is a `k`-piece (p. 316) if `x ∈ (1/(k + 1), 1/k]`. (For `k = 0` no real is a `0`-piece,
since `1/0 = 0` in Lean.) -/
def IsPiece (k : ℕ) (x : ℝ) : Prop := 1 / ((k : ℝ) + 1) < x ∧ x ≤ 1 / (k : ℝ)

/-- `w₁(x) = ⌊1/x⌋⁻¹` (p. 316). For `x ∈ (0, 1]` the integer `⌊1/x⌋` is the unique `k` with `x` a
`k`-piece, so `w₁(x) = 1/k`. -/
noncomputable def w1 (x : ℝ) : ℝ := ((⌊1 / x⌋₊ : ℕ) : ℝ)⁻¹

/-- `(x, y)` obeys relation `k` (p. 317) if `x` is a `k`-piece and `kx + y ≤ 1`. -/
def ObeysRelation (k : ℕ) (x y : ℝ) : Prop := IsPiece k x ∧ (k : ℝ) * x + y ≤ 1

/-- `w₂(x, y)` (p. 317): `w₁(x) + ((k − 1)/k) w₁(y)` if `(x, y)` obeys relation `k`, where `k` is
the piece type of `x`, and `w₁(x) + w₁(y)` otherwise. The relation uses the `k` of the first
(larger) element `x`; for `x ∈ (0, 1]` that `k` is `⌊1/x⌋`. -/
noncomputable def w2 (x y : ℝ) : ℝ :=
  if ObeysRelation ⌊1 / x⌋₊ x y then
    w1 x + (((⌊1 / x⌋₊ : ℕ) : ℝ) - 1) / ((⌊1 / x⌋₊ : ℕ) : ℝ) * w1 y
  else w1 x + w1 y

/-- The partitions of the positions `0, …, n - 1` into one- and two-element sets, encoded as the
involutions `σ` of `Fin n` (`σ * σ = 1`): the fixed points are the one-element sets and the
pairs `{i, σ i}` with `i ≠ σ i` the two-element sets. The set is finite and contains `σ = 1`. -/
noncomputable def pairings (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => σ * σ = 1)

/-- `w₁₂(π)` (p. 316) for a partition `π` (an involution `σ`) of the positions of a list `S`:
`Σ_{x ∈ π(1)} w₁(x) + Σ_{(x,y) ∈ π(2)} w₂(x, y)`, where `π(1)` are the fixed points and `π(2)`
the pairs `(S_i, S_{σ i})` with `i < σ i` (the paper's `index(x) < index(y)`). -/
noncomputable def w12 (S : List ℝ) (σ : Equiv.Perm (Fin S.length)) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => σ i = i), w1 (S.get i)) +
    ∑ i ∈ Finset.univ.filter (fun i => i < σ i), w2 (S.get i) (S.get (σ i))

/-- The weight `W(X) = min_π w₁₂(π)` (pp. 315–316), `π` ranging over all partitions of `X` into
one- and two-element sets. The elements are indexed in nonincreasing order (the paper's `L` is in
decreasing order), so each pair is oriented (larger, smaller); for equal values the orientation
does not affect `w₂`, and `W` depends only on the multiset `X`. The minimum is over the finite
nonempty set `pairings`, so it is attained. -/
noncomputable def W (X : List ℝ) : ℝ :=
  (pairings (sortDesc X).length).inf' ⟨1, by simp [pairings]⟩ (w12 (sortDesc X))

/-- The largest element of a bin (`0` for an empty bin; every bin of a packing is nonempty). -/
def binMax (B : List ℝ) : ℝ := B.foldr max 0

/-- A `k`-bin (p. 316): a bin whose largest element is a `k`-piece. -/
def IsKBin (k : ℕ) (B : List ℝ) : Prop := IsPiece k (binMax B)

/-- The final FFD bin (in `ffdPack L`) holding position `i` of the sorted list `sortDesc L`. -/
noncomputable def ffdBin (L : List ℝ) (i : Fin (sortDesc L).length) : List ℝ :=
  (ffdPack L).getD (ffBinOf (sortDesc L) i) []

/-- BASIC (p. 316): the positions `i` of the sorted list `sortDesc L` such that, for some `k`,
the item is a `k`-piece and lies in a `k`-bin of the FFD packing of `L`. -/
noncomputable def basic (L : List ℝ) : Finset (Fin (sortDesc L).length) :=
  Finset.univ.filter (fun i => ∃ k : ℕ, IsPiece k ((sortDesc L).get i) ∧ IsKBin k (ffdBin L i))

/-- SURPLUS `= L − BASIC` (p. 317), as positions of the sorted list. -/
noncomputable def surplus (L : List ℝ) : Finset (Fin (sortDesc L).length) :=
  Finset.univ \ basic L

end BinPacking.SmallItems
