import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- Lemma C-2, p. App-5: for `α ∈ [0, 1]`, `w > 0`, `q ∈ (0, 1)` and
`r ∈ [r̲_α(w, q), w) ∪ [w, r̄_α(w, q)]`, the price `r` is an optimal price of `F_α(·|r, (w, q))`:
it maximizes the revenue `v ↦ v F̄_α(v|r, (w, q))` over `v ≥ 0`. -/
theorem lemma_C_2 (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    r ∈ Set.Ici (0 : ℝ) ∧ IsMaxOn (fun v => v * Fbar α w q r v) (Set.Ici 0) r := by sorry

end SinglePointPricing.Det

