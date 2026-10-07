import Mathlib
import Definitions.Def_WeightedMajority_Randomized_WMRModel

open MeasureTheory

namespace WeightedMajority.Randomized

/-- Theorem 6.1 (p. 240): under the weak independence condition, the expected number of
mistakes of WMR is at most `E(ln(w_init/w_fin))/(1 − β)`. Expectations are lower Lebesgue
integrals, so the right-hand side may be `+∞`; `w_fin > 0` almost surely excludes the paper's
infinite-bound case. -/
theorem theorem_6_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam)
    (hfin : ∀ᵐ ω ∂P, 0 < totalWeight w1 F x ρ t ω) :
    ∫⁻ ω, ENNReal.ofReal (mistakes t lam ρ ω) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal
          (Real.log (totalWeight w1 F x ρ 0 ω / totalWeight w1 F x ρ t ω)) ∂P)
        / ENNReal.ofReal (1 - β) := by sorry

end WeightedMajority.Randomized

