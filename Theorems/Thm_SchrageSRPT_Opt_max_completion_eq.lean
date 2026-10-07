import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem max_completion_eq (A P : ℕ → ℝ) (δo δr : ℕ → ℝ → ℝ)
    (hδo : IsSchedule A δo) (hδr : IsSchedule A δr) (j k : ℕ) (t : ℝ) (hjk : j ≠ k)
    (hj : j ∈ inSystem A P δo t) (hk : k ∈ inSystem A P δo t)
    (hbefore : ∀ x, x < t → δr j x = δo j x ∧ δr k x = δo k x)
    (hsum : ∀ x, δr j x + δr k x = δo j x + δo k x)
    (hwaste_o : ∀ i, (i = j ∨ i = k) → ∀ x, remaining A P δo i x ≤ 0 → δo i x = 0)
    (hwaste_r : ∀ i, (i = j ∨ i = k) → ∀ x, remaining A P δr i x ≤ 0 → δr i x = 0) :
    max (completion A P δo k) (completion A P δo j) =
      max (completion A P δr k) (completion A P δr j) := by sorry
end SchrageSRPT.Opt

