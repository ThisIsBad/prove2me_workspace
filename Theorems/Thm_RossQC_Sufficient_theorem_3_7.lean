import Definitions.Def_RossQC_Sufficient_Model

namespace RossQC.Sufficient

/-- Ross, Theorem 3.7(a,b), pp. 592–593. A β-optimal stationary rule
selects a minimum of (3) at every admissible belief, including threshold
points. The printed bound `P₂ ≤ 1` in (a) is imposed when the optimal revise
region is nonempty; otherwise `P₂ > 1` allows that interval to be empty, as
the paper's proof explicitly permits. `0 < C` makes the displayed quotient
well-defined. Lean's zero-denominator convention applies when `π = 1`,
where `V_β(1) - V_β(π) = 0`; the two implications retain their intended
conclusions in that case. -/
theorem theorem_3_7 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ((1 - M.β) * (M.R + M.β * M.value M.π) / M.C ≤
        (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) →
      ∃ P₁ P₂ : ℝ, M.π ≤ P₁ ∧ P₁ ≤ P₂ ∧
        ((∃ P ∈ Set.Icc (0 : ℝ) 1,
            M.rhs3 M.value P .revise = M.value P) → P₂ ≤ 1) ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.threeRegion P₁ P₂ P) = M.value P) ∧
    ((M.I + M.β * (M.value 1 - M.value M.π) ≥
        M.C / (1 - M.β * (1 - M.π)) ∨
      (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) ≤
        (M.R / M.C) * (1 - M.β * (1 - M.π))) →
      ∃ P₁ : ℝ, M.π ≤ P₁ ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.twoRegion P₁ P) = M.value P) := by sorry

end RossQC.Sufficient

