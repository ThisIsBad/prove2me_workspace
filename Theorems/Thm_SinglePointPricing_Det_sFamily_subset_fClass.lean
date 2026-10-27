import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- §3, p. 14: every element of the worst-case family `S_{α,w,q}` is an `α`-strongly regular value
law with conversion rate `q` at `w`, i.e. `S_{α,w,q} ⊂ F_α(w, q)`. -/
theorem sFamily_subset_fClass (α w q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    SFamily α w q ⊆ FClass α w q := by sorry

end SinglePointPricing.Det

