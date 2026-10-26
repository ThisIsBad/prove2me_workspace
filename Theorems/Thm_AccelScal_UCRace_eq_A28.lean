import Mathlib
import Definitions.Def_AccelScal_UCRace_Setting

noncomputable section

namespace AccelScal.UCRace

/-- Lin, Appendix A.6, equations (A.27)–(A.28), p. 21. The strict
inequality requires a nonzero project surplus; it fails at the upper endpoint. -/
theorem eq_A28 (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) (R1 R2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    (let V := V1 T1 T2 r
     let lhs := V R1 R2 * deriv (fun b => deriv (fun a => V a b) R1) R2
       - deriv (fun a => V a R2) R1 * deriv (fun b => V R1 b) R2
     lhs = deriv T2.lam R2 * (T1.u R1 * T1.lam R1 - R1) ^ 2 /
         (r + T1.lam R1 + T2.lam R2) ^ 4 * deriv T1.lam R1 ∧
       (0 < T1.γ → 0 < T2.γ → T1.u R1 * T1.lam R1 ≠ R1 → 0 < lhs)) := by sorry

end AccelScal.UCRace

