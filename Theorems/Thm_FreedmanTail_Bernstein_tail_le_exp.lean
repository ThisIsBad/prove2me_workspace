import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), proof of (4.1) Theorem, pp. 107–108: under (3.4), for positive `a, b`
and every `λ ≥ 0`, `P{S_n ≥ a and T_n ≤ b for some n} ≤ exp[−λa + e(λ)b]`. -/
theorem tail_le_exp {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (lam : ℝ) (hlam : 0 ≤ lam) :
    P {ω | ∃ n, 1 ≤ n ∧ a ≤ S X n ω ∧ T ℱ X P n ω ≤ b}
      ≤ ENNReal.ofReal (Real.exp (-lam * a + e lam * b)) := by sorry

end FreedmanTail.Bernstein

