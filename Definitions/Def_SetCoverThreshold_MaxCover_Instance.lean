import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- An instance of **max k-cover** (p. 634): `n` points `Fin n`, a list of subsets of the points,
and the number `k` of subsets to be selected. -/
structure Instance where
  /-- The number of points. -/
  n : ℕ
  /-- The collection of subsets. -/
  sets : List (Finset (Fin n))
  /-- The number of subsets to select. -/
  k : ℕ

/-- The alphabet used to write instances. -/
inductive Sym where
  | zero
  | one
  | sep
  deriving DecidableEq

instance : Fintype Sym where
  elems := {Sym.zero, Sym.one, Sym.sep}
  complete := by intro x; cases x <;> simp

/-- The characteristic bit-vector of a set of points. -/
def encodeSet {n : ℕ} (S : Finset (Fin n)) : List Sym :=
  List.ofFn (fun p : Fin n => if p ∈ S then Sym.one else Sym.zero)

/-- Encoding of an instance: `n` in unary and a separator, then each set as its characteristic
bit-vector followed by a separator, then `k` in unary. -/
def encode (I : Instance) : List Sym :=
  List.replicate I.n Sym.one ++ (Sym.sep :: I.sets.flatMap (fun S => encodeSet S ++ [Sym.sep])) ++
    List.replicate I.k Sym.one

/-- The points covered by the sub-collection of sets with indices in `T`. -/
def coverOf (I : Instance) (T : Finset (Fin I.sets.length)) : Finset (Fin I.n) :=
  T.biUnion (fun i => I.sets.get i)

/-- `opt`: the largest number of points covered by at most `k` of the sets. -/
def opt (I : Instance) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin I.sets.length))).filter (fun T => T.card ≤ I.k)).sup
    (fun T => (coverOf I T).card)

/-- **Approximating max k-cover within a ratio `δ`** (p. 648, non-constructive): a
polynomial-time algorithm that on every input outputs (in unary) a number between `δ · opt`
and `opt`. -/
def MaxCoverApproximable (δ : ℝ) : Prop :=
  ∃ A : List Sym → List Unit, PolyTimeComputable A ∧
    ∀ I : Instance, δ * (opt I : ℝ) ≤ (A (encode I)).length ∧ (A (encode I)).length ≤ opt I

/-- A **greedy run** (p. 647): a sequence of `k` set indices, each covering the largest number of
points not covered by the sets selected before it (ties broken arbitrarily). -/
def IsGreedyRun (I : Instance) (run : Fin I.k → Fin I.sets.length) : Prop :=
  ∀ t : Fin I.k, ∀ j : Fin I.sets.length,
    (I.sets.get j \ coverOf I ((Finset.univ.filter (· < t)).image run)).card ≤
      (I.sets.get (run t) \ coverOf I ((Finset.univ.filter (· < t)).image run)).card

end SetCoverThreshold.MaxCover
