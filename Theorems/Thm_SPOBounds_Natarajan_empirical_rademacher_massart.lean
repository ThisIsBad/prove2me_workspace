import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SPOBounds_Natarajan_Rademacher
import Definitions.Def_SPOBounds_Natarajan_NatarajanDim

namespace SPOBounds.Natarajan

/-- **Proof of Theorem 2, Massart step** (arXiv:1905.11488v3, Appendix B.1, p. 31, the
displayed chain, fourth line). For a fixed sample `s` whose cost vectors lie in the nonempty
bounded set `C`, if the set `𝔉_{|𝕏}` of decision vectors `(w(f(x₁)), …, w(f(xₙ)))`, `f ∈ H`,
is finite, then `R̂ⁿ_SPO(H) ≤ ω_S(C) √(2 log |𝔉_{|𝕏}| / n)`. -/
theorem empirical_rademacher_massart {d : ℕ} {X : Type*}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (n : ℕ) (hn : 0 < n) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) (hsC : ∀ i, (s i).2 ∈ C)
    (hfin : (sampleDecisions w H s).Finite) :
    empRademacherSPO w H s ≤
      linGapSet S C * Real.sqrt (2 * Real.log ((sampleDecisions w H s).ncard : ℝ) / n) := by sorry

end SPOBounds.Natarajan
