import Mathlib

namespace BinPacking.Decreasing

/-- The standing hypothesis of the paper (p. 300): `L = (a₁, …, aₙ)` is a list of real numbers
in `(0, 1]`. Lists are read left to right and may repeat values. -/
def IsList (L : List ℝ) : Prop := ∀ a ∈ L, 0 < a ∧ a ≤ 1

/-- `L*` (p. 300): the minimum number `b` of unit bins such that the items of `L` can be assigned
to bins `0, …, b - 1` (a map `Fin L.length → Fin b`) with every bin sum at most `1`.
`sInf` on `ℕ` is `0` on the empty set; for a list satisfying `IsList` the set is nonempty
(`b = L.length` works), so `IsList` is assumed wherever `optBins` is used. `optBins [] = 0`. -/
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

/-- Best-fit choice (Algorithm 2, p. 300): the least index of a nonempty bin whose level `β`
satisfies `β + a ≤ 1` and is as large as possible among such bins; `bins.length` (a new bin) if
no nonempty bin fits. -/
noncomputable def bfChoice (bins : List (List ℝ)) (a : ℝ) : ℕ :=
  bins.findIdx (fun B => decide (B.sum + a ≤ 1 ∧ ∀ B' ∈ bins, B'.sum + a ≤ 1 → B'.sum ≤ B.sum))

/-- The run of an on-line placement rule `choose` on `L`: the items are placed in list order,
starting from no bins. The result is the list of nonempty bins `B₁, B₂, …` in index order. -/
noncomputable def run (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun bins a => placeAt bins (choose bins a) a) []

/-- `FF(L)` (p. 301): the number of bins used by first-fit (Algorithm 1) on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ := (run ffChoice L).length

/-- `BF(L)` (p. 301): the number of bins used by best-fit (Algorithm 2) on `L`. -/
noncomputable def BF (L : List ℝ) : ℕ := (run bfChoice L).length

/-- `L` arranged into nonincreasing order (Algorithms 3 and 4, p. 300), by a stable merge sort
with the comparison `b ≤ a`: equal items keep their relative order from `L`. -/
noncomputable def sortDesc (L : List ℝ) : List ℝ :=
  L.mergeSort (fun a b => decide (b ≤ a))

/-- `FFD(L)` (Algorithm 3, p. 300; notation p. 301): the number of bins used by first-fit
applied to `L` arranged into nonincreasing order. -/
noncomputable def FFD (L : List ℝ) : ℕ := FF (sortDesc L)

/-- `BFD(L)` (Algorithm 4, p. 300; notation p. 301): the number of bins used by best-fit
applied to `L` arranged into nonincreasing order. -/
noncomputable def BFD (L : List ℝ) : ℕ := BF (sortDesc L)

/-- History of a run: the (0-based) index of the bin into which item number `i` (0-based, the
paper's `a_{i+1}`) is placed. It is the rule's choice on the bins produced by the first `i`
items; it equals the number of bins so far when the item opens a new bin. -/
noncomputable def binOf (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (i : Fin L.length) : ℕ :=
  choose (run choose (L.take i)) (L.get i)

/-- History of a run: the (0-based) position that item number `i` fills inside its bin, i.e.
the number of items already in that bin just before item `i` is placed (`0` when it opens a new
bin). The paper's position `(j, k)` (p. 310) is `(binOf + 1, slotOf + 1)`. -/
noncomputable def slotOf (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (i : Fin L.length) : ℕ :=
  ((run choose (L.take i)).getD (binOf choose L i) []).length

end BinPacking.Decreasing
