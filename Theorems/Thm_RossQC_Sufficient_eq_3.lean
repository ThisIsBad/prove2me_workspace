import Definitions.Def_RossQC_Sufficient_Model
open Filter

namespace RossQC.Sufficient

/-- Ross, *Quality Control under Markovian Deterioration*, §3, equation (3),
p. 590 (unnumbered claim around the displayed equation). The finite-horizon
values from (4) converge to a bounded `V_β` satisfying (3) on the belief
interval. -/
theorem eq_3 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P))) ∧
    (∃ B : ℝ, ∀ P ∈ Set.Icc (0 : ℝ) 1, |M.value P| ≤ B) ∧
    (∀ P ∈ Set.Icc (0 : ℝ) 1,
      M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise))) := by sorry

end RossQC.Sufficient

