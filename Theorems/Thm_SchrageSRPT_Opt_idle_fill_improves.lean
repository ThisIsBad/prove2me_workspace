import Mathlib
import Definitions.Def_SchrageSRPT_Opt_Model

namespace SchrageSRPT.Opt
theorem idle_fill_improves (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (hδo : IsSchedule A δo)
    (j : ℕ) (t v : ℝ) (hv : 0 < v) (hj : j ∈ inSystem A P δo t)
    (hj_idle : ∀ x ∈ Set.Icc t (t + v), δo j x = 0)
    (hb1 : ∀ x ∈ Set.Icc t (t + v), ∀ k ∈ inSystem A P δo x, δo k x = 0)
    (hCj : completion A P δo j ≠ ⊤) :
    completion A P (idleFill δo j t v) j < completion A P δo j ∧
      ∀ i, i ≠ j → completion A P (idleFill δo j t v) i = completion A P δo i := by sorry
end SchrageSRPT.Opt

