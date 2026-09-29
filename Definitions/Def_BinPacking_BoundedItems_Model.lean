import Mathlib

namespace BinPacking.BoundedItems

open scoped ENNReal

/-- The standing hypothesis of Johnson–Demers–Ullman–Garey–Graham (1974), p. 300: a list
`L = (a₁, a₂, …, a_n)` of real numbers in `(0, 1]`. Lists are read left to right and may
repeat values. -/
def IsList (L : List ℝ) : Prop :=
  ∀ a ∈ L, 0 < a ∧ a ≤ 1

/-- `f` places the items of `L` (indexed `0, …, n − 1`) into `b` bins so that no bin contains
numbers whose sum exceeds `1`. -/
def IsPacking (L : List ℝ) (b : ℕ) (f : Fin L.length → Fin b) : Prop :=
  ∀ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1

/-- `L*` (p. 300): the minimum number of bins into which the elements of `L` can be placed so
that no bin contains numbers whose sum exceeds `1`. For a list satisfying `IsList` the set is
nonempty (`b = n`, one item per bin); `sInf ∅ = 0` on `ℕ`, so `IsList` must accompany every use.
`optBins [] = 0`. -/
noncomputable def optBins (L : List ℝ) : ℕ :=
  sInf {b : ℕ | ∃ f : Fin L.length → Fin b, IsPacking L b f}

/-- The level of a bin: the sum of its contents. -/
def level (B : List ℝ) : ℝ :=
  B.sum

/-- One First-Fit placement (Algorithm 1, p. 300). The argument is the list of nonempty bins
`B₁, B₂, …` opened so far, each holding its contents in placement order. The item `a` goes into
the first bin whose level `β` satisfies `β ≤ 1 − a` (i.e. `β + a ≤ 1`); if there is none, a new
bin `[a]` is opened after the existing ones. -/
noncomputable def ffInsert (a : ℝ) : List (List ℝ) → List (List ℝ)
  | [] => [[a]]
  | B :: Bs => if level B + a ≤ 1 then (B ++ [a]) :: Bs else B :: ffInsert a Bs

/-- The First-Fit packing of `L`: the items `a₁, a₂, …, a_n` are placed in that order. -/
noncomputable def ffPack (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun P a => ffInsert a P) []

/-- `FF(L)` (p. 301): the number of bins used by First-Fit on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ :=
  (ffPack L).length

/-- The Best-Fit choice (Algorithm 2, p. 300) for item `a` among the open bins `P`: the least
index `i` such that bin `i` has level `β ≤ 1 − a` and `β` is as large as possible among the bins
with that property; `none` if no open bin has room. -/
noncomputable def bfChoice (a : ℝ) (P : List (List ℝ)) : Option ℕ :=
  let fits := (List.range P.length).filter (fun i => decide (level (P.getD i []) + a ≤ 1))
  fits.find? (fun i => fits.all (fun j => decide (level (P.getD j []) ≤ level (P.getD i []))))

/-- One Best-Fit placement: put `a` into the bin chosen by `bfChoice`, or open a new bin `[a]`
after the existing ones if no open bin has room. -/
noncomputable def bfInsert (a : ℝ) (P : List (List ℝ)) : List (List ℝ) :=
  match bfChoice a P with
  | some i => P.set i (P.getD i [] ++ [a])
  | none => P ++ [[a]]

/-- The Best-Fit packing of `L`: the items `a₁, a₂, …, a_n` are placed in that order. -/
noncomputable def bfPack (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun P a => bfInsert a P) []

/-- `BF(L)` (p. 301): the number of bins used by Best-Fit on `L`. -/
noncomputable def BF (L : List ℝ) : ℕ :=
  (bfPack L).length

/-- `R^α_FF(k)` (p. 308): the supremum of `FF(L)/L*` over all lists `L ⊆ (0, α]` with `L* = k`,
taken in `ℝ≥0∞` (an empty family gives `0`, an unbounded one `⊤`). At `k = 0` the only such list
is the empty list, with `FF = 0`, so the value is `0`. -/
noncomputable def ratioFF (α : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : IsList L) (_ : ∀ a ∈ L, a ≤ α) (_ : optBins L = k),
    (FF L : ℝ≥0∞) / (k : ℝ≥0∞)

/-- `R^α_BF(k)` (p. 308): the supremum of `BF(L)/L*` over all lists `L ⊆ (0, α]` with `L* = k`,
taken in `ℝ≥0∞`. -/
noncomputable def ratioBF (α : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : IsList L) (_ : ∀ a ∈ L, a ≤ α) (_ : optBins L = k),
    (BF L : ℝ≥0∞) / (k : ℝ≥0∞)

end BinPacking.BoundedItems
