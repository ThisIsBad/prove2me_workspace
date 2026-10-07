import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), (4.1) Theorem, p. 107: suppose (3.4). For any positive numbers `a`, `b`,
`P{S_n ≥ a and T_n ≤ b for some n = 1, 2, ⋯} ≤ (b/(a+b))^{a+b} e^a ≤ exp[−a²/(2(a+b))]`. -/
theorem theorem_4_1 {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    P {ω | ∃ n, 1 ≤ n ∧ a ≤ S X n ω ∧ T ℱ X P n ω ≤ b}
        ≤ ENNReal.ofReal ((b / (a + b)) ^ (a + b) * Real.exp a) ∧
      (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by sorry

end FreedmanTail.Bernstein

