import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem num_in_system_of_completions (A P : ℕ → ℝ) (hfin : ∀ t : ℝ, {n | A n ≤ t}.Finite)
    (δo δr : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo) (hδr : IsSchedule A δr)
    (j k : ℕ) (hjk : j ≠ k)
    (h1 : ∀ i, i ≠ j → i ≠ k → completion A P δo i = completion A P δr i)
    (h2 : min (completion A P δr k) (completion A P δr j) <
      min (completion A P δo k) (completion A P δo j))
    (h3 : max (completion A P δr k) (completion A P δr j) =
      max (completion A P δo k) (completion A P δo j))
    (hjr : completion A P δr j ≤ completion A P δr k) :
    ∀ y : ℝ,
      (completion A P δr j ≤ (y : WithTop ℝ) ∧
          (y : WithTop ℝ) < min (completion A P δo k) (completion A P δo j) →
        numInSystem A P δr y + 1 = numInSystem A P δo y) ∧
      (¬ (completion A P δr j ≤ (y : WithTop ℝ) ∧
          (y : WithTop ℝ) < min (completion A P δo k) (completion A P δo j)) →
        numInSystem A P δr y = numInSystem A P δo y) := by sorry
end SchrageSRPT.Opt

