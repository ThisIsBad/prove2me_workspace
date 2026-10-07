import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace ProjSchedTW.Complexity

open CookPvsNP

/-! # Binary encodings and the three source problems of the reductions

Neumann, Schwindt & Zimmermann reduce from PARTITION (proof of Theorem 2.12.1, p. 131), from
SUBSET SUM (proof of Proposition 2.5.4, p. 48) and from SIMPLE MAX CUT (proof of Proposition
3.4.2, p. 241), all "cf. Garey and Johnson, 1979". Instances are written over a four-letter
alphabet, every number in binary, so that the size of an instance is the length of its code. -/

/-- The four-letter alphabet of instance codes: the binary digits `0`, `1`, a minus sign, and a
separator that ends the code of each number. -/
inductive BSym where
  | zero
  | one
  | minus
  | sep
  deriving DecidableEq

instance : Fintype BSym where
  elems := {BSym.zero, BSym.one, BSym.minus, BSym.sep}
  complete := by intro x; cases x <;> simp

instance : Nonempty BSym := ⟨BSym.zero⟩

/-- A natural number `k` in binary: its binary digits, least significant first and without
leading zeros (`Nat.bits`; the empty digit string for `k = 0`), followed by a separator. -/
def encNat (k : ℕ) : List BSym :=
  (Nat.bits k).map (fun b => if b then BSym.one else BSym.zero) ++ [BSym.sep]

/-- An integer `z` in binary: a minus sign if `z < 0`, then the binary code of `|z|`. -/
def encInt (z : ℤ) : List BSym :=
  (if z < 0 then [BSym.minus] else []) ++ encNat z.natAbs

/-- A list of natural numbers, each in binary, one after the other. -/
def encNats (xs : List ℕ) : List BSym := xs.flatMap encNat

/-- A list of integers, each in binary, one after the other. -/
def encInts (xs : List ℤ) : List BSym := xs.flatMap encInt

/-! ## PARTITION -/

/-- A PARTITION instance with sizes `s(1), …, s(ν) ∈ ℕ` (the list `s`, `ν = s.length`) is a
yes-instance iff the index set can be split into two parts `I'`, `I''` of equal total size. -/
def PartitionYes (s : List ℕ) : Prop :=
  ∃ A : Finset (Fin s.length), ∑ i ∈ A, s.get i = ∑ i ∈ Aᶜ, s.get i

/-- The PARTITION language: binary codes `s(1) s(2) … s(ν)` of the yes-instances. -/
def partitionLang : Lang BSym :=
  { w | ∃ s : List ℕ, PartitionYes s ∧ w = encNats s }

/-! ## SUBSET SUM -/

/-- A SUBSET SUM instance with sizes `s(1), …, s(ν) ∈ ℕ` and threshold `M ∈ ℕ` is a
yes-instance iff some subset of the indices has total size exactly `M`. -/
def SubsetSumYes (s : List ℕ) (M : ℕ) : Prop :=
  ∃ A : Finset (Fin s.length), ∑ i ∈ A, s.get i = M

/-- The SUBSET SUM language: binary codes `M s(1) … s(ν)` of the yes-instances. -/
def subsetSumLang : Lang BSym :=
  { w | ∃ (s : List ℕ) (M : ℕ), SubsetSumYes s M ∧ w = encNats (M :: s) }

/-! ## SIMPLE MAX CUT -/

open Classical in
/-- The number of edges of the simple graph `G` on the nodes `Fin ν` that join a node of `A` to
a node of its complement (each edge `{i, j}` counted once, as the pair with `i < j`). -/
noncomputable def cutSize {ν : ℕ} (G : SimpleGraph (Fin ν)) (A : Finset (Fin ν)) : ℕ :=
  (Finset.univ.filter fun e : Fin ν × Fin ν =>
    e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ (e.1 ∈ A ↔ e.2 ∉ A)).card

/-- A SIMPLE MAX CUT instance, a graph `G` and a number `M`, is a yes-instance iff there is a
partition of the nodes into `A` and its complement with at least `M` edges between the parts. -/
def MaxCutYes {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) : Prop :=
  ∃ A : Finset (Fin ν), M ≤ cutSize G A

open Classical in
/-- The code of a SIMPLE MAX CUT instance: `ν`, the adjacency matrix row by row (`1` for an edge,
`0` otherwise), then `M`, all in binary. -/
noncomputable def maxCutCode {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) : List BSym :=
  encNats ([ν] ++ (List.ofFn fun i : Fin ν => List.ofFn fun j : Fin ν =>
    if G.Adj i j then 1 else 0).flatten ++ [M])

/-- The SIMPLE MAX CUT language: codes of the yes-instances. -/
def maxCutLang : Lang BSym :=
  { w | ∃ (ν : ℕ) (G : SimpleGraph (Fin ν)) (M : ℕ), MaxCutYes G M ∧ w = maxCutCode G M }

end ProjSchedTW.Complexity
