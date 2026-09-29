import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.SetCover

/-- A partition system `B(m, L, k, d)` (Feige 1998, Definition 3.1, pp. 643–644), on the ground
set `Fin m` with partitions indexed by `Fin L`. Point `b` lies in subset `part b j` of partition
`j`, so every partition is a collection of `k` disjoint subsets whose union is the ground set.
* `distinct`: the `L` partitions are distinct (two different indices never induce the same
  partition of the ground set into blocks);
* `cover_bound`: any cover of the `m` points by subsets (pairs `(j, i)` = subset `i` of
  partition `j`) that appear in pairwise different partitions has at least `d` members. -/
structure PartitionSystem (m L k d : ℕ) where
  part : Fin m → Fin L → Fin k
  distinct : ∀ j j' : Fin L, j ≠ j' →
    ¬ ∀ b b' : Fin m, (part b j = part b' j ↔ part b j' = part b' j')
  cover_bound : ∀ F : Finset (Fin L × Fin k),
    (∀ x ∈ F, ∀ y ∈ F, x.1 = y.1 → x = y) →
    (∀ b : Fin m, ∃ x ∈ F, part b x.1 = x.2) → d ≤ F.card

namespace PartitionSystem

variable {m L k d : ℕ}

/-- The table of a partition system: row `b` lists, for each partition `j`, the index of the
subset containing point `b`. -/
def table (P : PartitionSystem m L k d) : List (List (Fin k)) :=
  List.ofFn fun b : Fin m => List.ofFn fun j : Fin L => P.part b j

end PartitionSystem

/-- String encoding of a table over the alphabet `Option (Fin k)`: each row is written symbol by
symbol and terminated by the separator `none`. -/
def encodeTable {k : ℕ} (T : List (List (Fin k))) : List (Option (Fin k)) :=
  T.flatMap fun row => row.map some ++ [none]

/-- Unary encoding of a pair `(m, L)`: `1^m 0 1^L`. -/
def unaryPair (m L : ℕ) : List Bool :=
  List.replicate m true ++ false :: List.replicate L true

/-- The deterministic construction of partition systems of Naor, Schulman and Srinivasan (1995,
Theorem 9), in the form Feige 1998 uses it (p. 644), taken as a hypothesis: for every `η > 0`
there is `k₀` such that for every `k ≥ k₀` and every exponent `a` there are `m₀` and a
polynomial-time computable map which, on input `(m, L)` in unary with `m ≥ m₀` and
`L ≤ (⌊log₂ m⌋)^a`, outputs the table of a partition system `B(m', L, k, d)` with `m ≤ m'` and
`d ≥ (1 - η) k ln m'`. -/
def NaorPartitionSystems : Prop :=
  ∀ η : ℝ, 0 < η → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a : ℕ, ∃ m₀ : ℕ,
    ∃ F : List Bool → List (Option (Fin k)), CookPvsNP.PolyTimeComputable F ∧
      ∀ m L : ℕ, m₀ ≤ m → L ≤ (Nat.log 2 m) ^ a →
        ∃ (m' d : ℕ) (P : PartitionSystem m' L k d),
          m ≤ m' ∧ F (unaryPair m L) = encodeTable P.table ∧
            (1 - η) * k * Real.log m' ≤ d

end SetCoverThreshold.SetCover
