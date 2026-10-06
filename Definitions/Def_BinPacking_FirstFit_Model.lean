import Mathlib

namespace BinPacking.FirstFit

open scoped ENNReal

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

/-- Best-fit choice (Algorithm 2, p. 300): the least index of a nonempty bin whose level `β`
satisfies `β + a ≤ 1` and is as large as possible among such bins; `bins.length` (a new bin) if
no nonempty bin fits. -/
noncomputable def bfChoice (bins : List (List ℝ)) (a : ℝ) : ℕ :=
  bins.findIdx (fun B => decide (B.sum + a ≤ 1 ∧ ∀ B' ∈ bins, B'.sum + a ≤ 1 → B'.sum ≤ B.sum))

/-- The run of an on-line placement rule `choose` on `L`: the items are placed in list order,
starting from no bins. The result is the list of nonempty bins `B₁, B₂, …` in index order. -/
noncomputable def run (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun bins a => placeAt bins (choose bins a) a) []

/-- The completed first-fit packing of `L`. -/
noncomputable def ffPack (L : List ℝ) : List (List ℝ) := run ffChoice L

/-- The completed best-fit packing of `L`. -/
noncomputable def bfPack (L : List ℝ) : List (List ℝ) := run bfChoice L

/-- `FF(L)` (p. 301): the number of bins used by first-fit on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ := (ffPack L).length

/-- `BF(L)` (p. 301): the number of bins used by best-fit on `L`. -/
noncomputable def BF (L : List ℝ) : ℕ := (bfPack L).length

/-- History of a run: the (0-based) index of the bin into which item number `i` (0-based, the
paper's `a_{i+1}`) is placed. It is the rule's choice on the bins produced by the first `i` items. -/
noncomputable def binOf (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (i : Fin L.length) : ℕ :=
  choose (run choose (L.take i)) (L.get i)

/-- History of a run: the level of the bin receiving item number `i`, just before that item is
placed (`0` when the item opens a new bin). -/
noncomputable def levelBefore (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ)
    (i : Fin L.length) : ℝ :=
  ((run choose (L.take i)).getD (binOf choose L i) []).sum

/-- Coarseness (p. 305) of bin number `j` (0-based) of a completed packing `P`: the largest `α`
such that some bin with smaller index is filled to level `1 - α`, i.e.
`max_{j' < j} (1 - level of bin j')`; the coarseness of the first bin is `0`. (The maximum is
taken together with `0`; in every packing produced by FF or BF all levels are at most `1`, so
this changes nothing.) -/
def coarseness (P : List (List ℝ)) (j : ℕ) : ℝ :=
  ((P.take j).map (fun B => 1 - B.sum)).foldr max 0

/-- `R_FF(k)` (p. 301): the supremum of `FF(L)/L*` over all lists `L` (of reals in `(0, 1]`) with
`L* = k`, computed in `ℝ≥0∞` so that an empty or unbounded family is not silently `0`.
At `k = 0` the only such list is the empty one, and the value is `0/0 = 0`. -/
noncomputable def ratioFF (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : IsList L) (_ : optBins L = k), (FF L : ℝ≥0∞) / (k : ℝ≥0∞)

/-- `R_BF(k)` (p. 301): the supremum of `BF(L)/L*` over all lists `L` with `L* = k`, in `ℝ≥0∞`. -/
noncomputable def ratioBF (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : IsList L) (_ : optBins L = k), (BF L : ℝ≥0∞) / (k : ℝ≥0∞)

end BinPacking.FirstFit
