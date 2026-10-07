import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic

universe u

namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- Proposition 3.2.1 (3.2.4): a universal `q₀` such that for every integer `q ≥ q₀`
(and `q ≥ 2`, the standing assumption of Section 3) the bound holds on every product
probability space. `log` is the natural logarithm. -/
theorem proposition_3_2_1 :
    ∃ q₀ : ℝ, ∀ (q : ℕ), 2 ≤ q → q₀ ≤ (q : ℝ) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
        (A : Set (Fin N → Ω)) (k : ℕ), MeasurableSet A →
        Measurable (qDist (fun _ : Fin q => A)) →
        (Measure.pi fun _ : Fin N => μ) {x | (k : ℕ∞) ≤ qDist (fun _ : Fin q => A) x} ≤
          ENNReal.ofReal (Real.exp 1 / ((Real.exp 1 - 1) * q * Real.log q)) ^ k *
            ((Measure.pi fun _ : Fin N => μ) A)⁻¹ ^ ((q : ℝ) * Real.log q) := by sorry

end TalagrandConc.QPoints

