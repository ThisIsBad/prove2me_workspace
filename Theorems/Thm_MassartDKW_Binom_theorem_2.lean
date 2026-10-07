import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

open MeasureTheory ProbabilityTheory

namespace MassartDKW.Binom

/-- Massart (1990), Theorem 2, p. 1271: if `S` has the binomial law `Bin(n, p)` and `q = 1 − p`,
then for every `ε` with `0 < ε ≤ q`,
`P(S − np > nε) ≤ exp(−nε²/(2(p + ε/3)(q − ε/3)))`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : unitInterval) (S : Ω → ℕ) (hS : HasLaw S (binomial n p) P)
    (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 - (p : ℝ)) :
    P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ε ^ 2) /
        (2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3)))) := by sorry

end MassartDKW.Binom

