import Mathlib

/-!
# 3-PARTITION

Błażewicz, Lenstra & Rinnooy Kan (1983), p. 16 (proof of Theorem 4), with the bounds
`¼b < a_j < ½b` assumed in the proof of Theorem 7 (p. 18); this is Garey & Johnson's SP15.
Indices are 0-based: `S = Fin (3t)` and the parts are indexed by `Fin t`.
-/

namespace ResourceScheduling.Chain

/-- An instance of 3-PARTITION: `t`, `b` and numbers `a_j` for `j ∈ S = {0, …, 3t − 1}`. -/
structure ThreePartition where
  /-- the number of parts -/
  t : ℕ
  /-- the target sum of each part -/
  b : ℕ
  /-- the numbers `a_j` -/
  a : Fin (3 * t) → ℕ

namespace ThreePartition

variable (P : ThreePartition)

/-- The instance is well formed: `b` is positive, `∑_{j ∈ S} a_j = t b`, and `¼b < a_j < ½b` for
every `j` (so every `a_j` is positive). -/
def Valid : Prop :=
  0 < P.b ∧ (∑ j, P.a j = P.t * P.b) ∧ ∀ j, P.b < 4 * P.a j ∧ 2 * P.a j < P.b

/-- `σ` assigns each index to a part `S_i = σ⁻¹(i)`; it is a solution when every part has exactly
three elements and sums to `b`. -/
def IsSolution (σ : Fin (3 * P.t) → Fin P.t) : Prop :=
  ∀ i, (Finset.univ.filter fun j => σ j = i).card = 3 ∧
    ∑ j ∈ Finset.univ.filter (fun j => σ j = i), P.a j = P.b

/-- `S` can be partitioned into `t` disjoint 3-element subsets, each summing to `b`. -/
def HasSolution : Prop := ∃ σ, P.IsSolution σ

/-- Yes-instances of 3-PARTITION. -/
def IsYes : Prop := P.Valid ∧ P.HasSolution

/-- The numbers of the instance: `t`, `b`, `a_0, …, a_{3t−1}`. -/
def code : List ℕ := [P.t, P.b] ++ List.ofFn P.a

end ThreePartition

end ResourceScheduling.Chain
