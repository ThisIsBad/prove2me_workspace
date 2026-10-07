import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

open MeasureTheory ProbabilityTheory

namespace MassartDKW.Binom

/-- Massart (1990), Comment 3, p. 1273 (Cramér–Chernoff bound): if `S` has the binomial law
`Bin(n, p)` with `0 < p` and `0 < ε ≤ q = 1 − p`, then `P(S − np > nε) ≤ exp(−n h(p, ε))`. -/
theorem comment_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : unitInterval) (S : Ω → ℕ) (hS : HasLaw S (binomial n p) P)
    (hp : 0 < (p : ℝ)) (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 - (p : ℝ)) :
    P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * h (p : ℝ) ε))) := by sorry

end MassartDKW.Binom

