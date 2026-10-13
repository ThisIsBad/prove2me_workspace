import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model
open Filter

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, §3, equation (3),
p. 590, specialized from the uniqueness assertion following equation (1), p. 588.
Formalization Note: `value` is the limit of (4). Convergence and boundedness
are explicit, and uniqueness ranges over bounded functions on the state space
`[0,1]`. The good-state cost is zero, while `C` is the bad-state cost. -/
theorem equation_3 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P))) ∧
    (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |M.value P| ≤ B) ∧
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise))) ∧
    (∀ W : ℝ → ℝ,
      (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |W P| ≤ B) →
      (∀ P ∈ Set.Icc (0 : ℝ) 1,
        W P = min (M.rhs3 W P .produce)
          (min (M.rhs3 W P .inspect) (M.rhs3 W P .revise))) →
      ∀ P ∈ Set.Icc (0 : ℝ) 1, W P = M.value P) := by sorry

end RossQC.AlwaysProduce

