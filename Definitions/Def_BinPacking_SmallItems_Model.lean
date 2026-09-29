import Mathlib

namespace BinPacking.SmallItems

/-- The standing hypothesis of the paper (p. 300): `L = (a₁, …, aₙ)` is a list of real numbers
in `(0, 1]`. Lists are read left to right and may repeat values. -/
def IsList (L : List ℝ) : Prop := ∀ a ∈ L, 0 < a ∧ a ≤ 1

/-- `L*` (p. 300): the minimum number `b` of unit bins such that the items of `L` can be assigned
to bins `0, …, b - 1` (a map `Fin L.length → Fin b`) with every bin sum at most `1`.
`sInf` on `ℕ` is `0` on the empty set; for a list satisfying `IsList` the set is nonempty
(`b = L.length` works), so `IsList` is assumed wherever `optBins` is used. -/
noncomputable def optBins (L : List ℝ) : ℕ :=
  sInf {b : ℕ | ∃ f : Fin L.length → Fin b, ∀ j : Fin b,
    ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}

/-- Place item `a` into bin number `j` (0-based) of the current list of nonempty bins; if `j` is
not the index of an existing bin, open a new bin `[a]` at the end. Each bin records its contents
in placement order. -/
def placeAt (bins : List (List ℝ)) (j : ℕ) (a : ℝ) : List (List ℝ) :=
  if j < bins.length then bins.mapIdx (fun i B => if i = j then B ++ [a] else B)
  else bins ++ [[a]]

/-- First-fit choice (Algorithm 1, p. 300): the least index of a nonempty bin whose level
`β` satisfies `β ≤ 1 - a`, i.e. `β + a ≤ 1`; `bins.length` (a new bin) if there is none. -/
noncomputable def ffChoice (bins : List (List ℝ)) (a : ℝ) : ℕ :=
  bins.findIdx (fun B => decide (B.sum + a ≤ 1))

/-- The first-fit run on `L`: the items are placed in list order, starting from no bins.
The result is the list of nonempty bins `B₁, B₂, …` in index order. -/
noncomputable def ffPack (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun bins a => placeAt bins (ffChoice bins a) a) []

/-- `FF(L)` (p. 301): the number of bins used by first-fit on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ := (ffPack L).length

/-- History of the first-fit run: the (0-based) index of the bin into which item number `i`
(0-based, the paper's `a_{i+1}`) is placed. It is first-fit's choice on the bins produced by the
first `i` items. Bins are never reordered, so it is also the item's bin in the final packing. -/
noncomputable def ffBinOf (L : List ℝ) (i : Fin L.length) : ℕ :=
  ffChoice (ffPack (L.take i)) (L.get i)

/-- The list `L` arranged into nonincreasing order (the first step of Algorithm 3, p. 300). -/
noncomputable def sortDesc (L : List ℝ) : List ℝ :=
  L.mergeSort (fun a b => decide (b ≤ a))

/-- The first-fit decreasing packing of `L` (Algorithm 3, p. 300): first-fit applied to the
nonincreasing rearrangement of `L`. -/
noncomputable def ffdPack (L : List ℝ) : List (List ℝ) := ffPack (sortDesc L)

/-- `FFD(L)` (p. 301): the number of bins used by first-fit decreasing on `L`. -/
noncomputable def FFD (L : List ℝ) : ℕ := FF (sortDesc L)

end BinPacking.SmallItems
