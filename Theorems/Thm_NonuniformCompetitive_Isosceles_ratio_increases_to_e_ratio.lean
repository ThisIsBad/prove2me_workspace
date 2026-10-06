import Mathlib
import Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio

namespace NonuniformCompetitive.Isosceles

/-- §5, p. 566 (Karlin–Manasse–McGeoch–Owicki 1994): the competitive ratio of Theorem 12 grows
and approaches `e/(e - 1)` as `d` grows. "Grows" is read as strictly increasing over the
admissible values `d = 1, 2, 3, …`, stated as strict monotonicity of `n ↦ isoscelesRatio (n + 1)`;
the limit is taken as `d → ∞`. -/
theorem ratio_increases_to_e_ratio :
    StrictMono (fun n : ℕ => isoscelesRatio (n + 1)) ∧
      Filter.Tendsto isoscelesRatio Filter.atTop
        (nhds (Real.exp 1 / (Real.exp 1 - 1))) := by sorry

end NonuniformCompetitive.Isosceles

