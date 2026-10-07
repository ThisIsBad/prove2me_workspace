import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem srpt_reassign_min_lt (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo)
    (j k : ℕ) (t v : ℝ) (hv : 0 < v) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hk_served : ∀ x ∈ Set.Icc t (t + v), δo k x = 1)
    (hS : remaining A P δo j t < remaining A P δo k t)
    (hfinite : min (completion A P δo k) (completion A P δo j) ≠ ⊤) :
    min (completion A P (srptReassign A P δo j k t) k)
        (completion A P (srptReassign A P δo j k t) j) <
      min (completion A P δo k) (completion A P δo j) := by sorry
end SchrageSRPT.Opt

