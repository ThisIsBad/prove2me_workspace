import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

open MeasureTheory

/-- Theorem 1 (Fundamental Reduction), p. 14: for `α ∈ [0, 1]`, `q ∈ (0, 1)` and every class
`P′ ⊆ P` of pricing mechanisms, `R(P′, F_α(w, q)) = R(P′, S_{α,w,q})`. -/
theorem theorem_1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (w : ℝ) (hw : 0 < w) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (P' : Set (Measure ℝ)) (hP' : ∀ Ψ ∈ P', IsMech Ψ) :
    maximin P' (FClass α w q) = maximin P' (SFamily α w q) := by sorry

end SinglePointPricing.Det

