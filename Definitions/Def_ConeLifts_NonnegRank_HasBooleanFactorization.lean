import Mathlib
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_NonnegRank_slackOperator

namespace ConeLifts.NonnegRank

/-- A **Boolean factorization of `supp(S_C)` of intermediate dimension `k`** (Gouveia, Parrilo &
Thomas, arXiv:1111.3164v2, Definition 4.10 and Theorem 4.11, p. 15). `supp(S_C)` is the 0/1 matrix
with a one exactly where `S_C(x, y) ≠ 0`; a Boolean factorization `supp(S_C) = AB` with
`A ∈ {0,1}^{ext(C) × k}`, `B ∈ {0,1}^{k × ext(C°)}` in Boolean arithmetic is encoded, as in the proof
of Theorem 4.11, by the row `A x ⊆ [k]` and the column `B y ⊆ [k]` as subsets of `Fin k`: the
Boolean product entry is one iff `A x ∩ B y ≠ ∅`. -/
def HasBooleanFactorization {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ A B : EuclideanSpace ℝ (Fin n) → Finset (Fin k),
    ∀ x ∈ Set.extremePoints ℝ C, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      (slackOperator x y ≠ 0 ↔ (A x ∩ B y).Nonempty)

end ConeLifts.NonnegRank
