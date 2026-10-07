import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem srpt_reassign_min_le (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hS : remaining A P δo j t < remaining A P δo k t) :
    min (completion A P (srptReassign A P δo j k t) k)
        (completion A P (srptReassign A P δo j k t) j) ≤
      min (completion A P δr k) (completion A P δr j) := by sorry
end SchrageSRPT.Opt

