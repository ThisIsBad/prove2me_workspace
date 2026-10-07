import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 299, display (3) in the proof of Lemma 4: let `t*` be such that every
vector system `(U', V')` of a submatrix `A'` obtained by deleting one row or one column of `A`
satisfies `max V'(t) − min U'(t) < ½εt` for `t ≥ t*`. If some row or some column of `A` is not
eligible in `(s, s + t*)` for the vector system `(U, V)`, then
`max V(s+t*) − min U(s+t*) < max V(s) − min U(s) + ½εt*`. -/
theorem eq3 [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (ε : ℝ) (hε : 0 < ε) (tstar : ℕ)
    (hrowIH : ∀ k : ι, ∀ (_ : Nonempty {i // i ≠ k}) (U' : ℕ → κ → ℝ)
      (V' : ℕ → {i // i ≠ k} → ℝ),
      IsVectorSystem (A.submatrix Subtype.val id) U' V' →
        ∀ t : ℕ, tstar ≤ t → vmax (V' t) - vmin (U' t) < ε / 2 * t)
    (hcolIH : ∀ k : κ, ∀ (_ : Nonempty {j // j ≠ k}) (U' : ℕ → {j // j ≠ k} → ℝ)
      (V' : ℕ → ι → ℝ),
      IsVectorSystem (A.submatrix id Subtype.val) U' V' →
        ∀ t : ℕ, tstar ≤ t → vmax (V' t) - vmin (U' t) < ε / 2 * t)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s : ℕ)
    (hnot : (∃ i, ¬ RowEligible V i s (s + tstar)) ∨ (∃ j, ¬ ColEligible U j s (s + tstar))) :
    vmax (V (s + tstar)) - vmin (U (s + tstar)) <
      vmax (V s) - vmin (U s) + ε / 2 * tstar := by sorry

end RobinsonFP.Convergence

