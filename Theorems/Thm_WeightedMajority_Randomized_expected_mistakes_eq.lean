import Mathlib
import Definitions.Def_WeightedMajority_Randomized_WMRModel

open MeasureTheory

namespace WeightedMajority.Randomized

/-- §6, p. 240, proof of Theorem 6.1: under the weak independence condition the conditional
expected mistake indicator of each trial is `|γ^{(j)} − ρ^{(j)}|`, and the expected number of
mistakes of WMR equals the expected total loss `E(Σ_j |γ^{(j)} − ρ^{(j)}|)`. -/
theorem expected_mistakes_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam) :
    (∀ j < t, P[fun ω => |lam j ω - ρ j ω| | history x ρ j]
        =ᵐ[P] fun ω => |gamma w1 F x ρ j ω - ρ j ω|) ∧
    ∫ ω, mistakes t lam ρ ω ∂P
      = ∫ ω, ∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω| ∂P := by sorry

end WeightedMajority.Randomized

