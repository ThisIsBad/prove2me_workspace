import Mathlib
import Definitions.Def_RossQC_AlwaysProduce_Model

namespace RossQC.AlwaysProduce

/-- Ross, *Quality Control under Markovian Deterioration*, Theorem 3.4(a,b),
p. 592. Formalization Note: `psi` is the discounted series cost of `R⁰`;
`R⁰` is β-optimal exactly when it equals `value` throughout `[0,1]`.
“Every β-optimal policy revises” is represented by revision being the unique
minimizer of equation (3). “Near 1” is a one-sided neighborhood in `[0,1]`.
`0 < C` makes explicit the positive bad-state cost implicit in the model. -/
theorem theorem_3_4 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ((∀ P ∈ Set.Icc (0 : ℝ) 1, M.psi P = M.value P) ↔
      M.C / (1 - M.β * (1 - M.π)) ≤ M.R) ∧
    (M.R < M.C / (1 - M.β * (1 - M.π)) →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1, 1 - ε < P →
          M.rhs3 M.value P .revise < M.rhs3 M.value P .produce ∧
          M.rhs3 M.value P .revise < M.rhs3 M.value P .inspect) := by sorry

end RossQC.AlwaysProduce

