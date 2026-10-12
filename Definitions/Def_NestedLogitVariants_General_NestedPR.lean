import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model

namespace NestedLogitVariants.General

open Classical

variable {ι : Type*} {n : ℕ}

/-- `(v_il, l)` precedes `(v_ij, j)` lexicographically. -/
def weightLt (I : Instance ι n) (i : ι) (l j : Fin n) : Prop :=
  I.v i l < I.v i j ∨ (I.v i l = I.v i j ∧ l < j)

/-- The products with the `k` smallest preference weights in nest `i`. -/
noncomputable def smallK (I : Instance ι n) (i : ι) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (Finset.univ.filter (fun l => weightLt I i l j)).card < k)

/-- `N^k_ij`: the first `j` products (index = revenue order) among `smallK I i k`. -/
noncomputable def nestedPR (I : Instance ι n) (i : ι) (k j : ℕ) : Finset (Fin n) :=
  (smallK I i k).filter (fun l => ((smallK I i k).filter (fun l' => l' < l)).card < j)

/-- The candidate collection of nest `i` used in Theorem 11 (pp. 25–26):
`{N^k_ij : k ∈ N, j = 0, …, k} ∪ {{j} : j ∈ N}`, with `k` ranging over `1, …, n` and
`N^k_i0 = ∅`. -/
def candidatesPR (I : Instance ι n) (i : ι) : Set (Finset (Fin n)) :=
  {S | (∃ k ∈ Finset.Icc 1 n, ∃ j ≤ k, S = nestedPR I i k j) ∨ ∃ j, S = {j}}

end NestedLogitVariants.General
