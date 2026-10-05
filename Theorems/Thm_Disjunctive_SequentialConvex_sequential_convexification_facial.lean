import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic
import Definitions.Def_Disjunctive_SequentialConvex_Fseq

namespace Disjunctive.SequentialConvex

/-- Theorem 3.1 (Balas §3.1, p. 42): if the disjunctive program `DP` is facial, then the
recursive sequential-convexification construction, applied in any order of `S`, terminates at
`conv F`. -/
theorem sequential_convexification_facial {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) {S : Type*} [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)]
    (d : (j : S) → Qidx j → Fin n → ℝ) (d0 : (j : S) → Qidx j → ℝ)
    (σ : Fin (Fintype.card S) ≃ S) (hFacial : Facial A b Qidx d d0) :
    Fseq Qidx (F0Set A b) d d0 σ (Fintype.card S) =
      convexHull ℝ (DisjunctiveConstraintSet A b Qidx d d0) := by sorry

end Disjunctive.SequentialConvex

