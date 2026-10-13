import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- The rows of `(A,B,b)` that are tight (satisfied at equality) throughout a target set,
e.g. throughout `Q` itself or throughout a facet `FQ` of `Q` (Balas §2.2.2, p. 29: "the equality
subsystem of `Q`", generalized here to an arbitrary target set so the same definition also gives
a facet's own equality subsystem, needed by Corollaries 2.8-2.10). -/
def TightRows {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) (target : Set ((Fin p → ℝ) × (Fin q → ℝ))) : Set (Fin m) :=
  {i | ∀ ux ∈ target, A.mulVec ux.1 i + B.mulVec ux.2 i = b i}

/-- `rank(A=, B=)` for the equality-subsystem rows `rows` (Balas §2.2.2, p. 29, `r`). -/
noncomputable def SystemRank {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (rows : Set (Fin m)) : ℕ :=
  (Matrix.fromCols (A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) id)
                    (B.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) id)).rank

/-- `rank(A=)` for the equality-subsystem rows `rows` (Balas §2.2.2, p. 29, `r*`). -/
noncomputable def SystemRankA {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (rows : Set (Fin m)) :
    ℕ :=
  (A.submatrix (Subtype.val : {i // i ∈ rows} → Fin m) id).rank

/-- `r := rank(A=, B=)` for `Q` itself (Balas §2.2.2, p. 29). -/
noncomputable def EqRank {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) : ℕ :=
  SystemRank A B (TightRows A B b (Poly2 A B b))

/-- `r* := rank(A=)` for `Q` itself (Balas §2.2.2, p. 29). -/
noncomputable def EqRankA {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ)
    (b : Fin m → ℝ) : ℕ :=
  SystemRankA A (TightRows A B b (Poly2 A B b))

end Disjunctive.Polarity
