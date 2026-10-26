import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic

namespace PrescAnalytics.ERM

open MeasureTheory

/-- Theorem 14, (30) (p. 41), with the corrected boundedness `0 ≤ g ≤ ḡ`. Let `G` be a pointwise
separable class of measurable functions `U → ℝ` with values in `[0, ḡ]`, `P` a probability measure on
`U`, `N ≥ 1`, `δ > 0`. Outside a set of `P^N`-measure at most `δ`, every sample
`S_N = (u^1, …, u^N)` satisfies
`E[g(T)] ≤ (1/N) Σ_i g(u^i) + 3ḡ √(log(2/δ)/(2N)) + ℜ̂_N(G; S_N)` for all `g ∈ G` simultaneously,
with the empirical complexity `ℜ̂_N(G; S_N) ∈ EReal`. -/
theorem theorem_14_eq30 {U : Type*} [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (G : Set (U → ℝ)) (gbar : ℝ) (hG_meas : ∀ g ∈ G, Measurable g)
    (hG_sep : IsPointwiseSeparable G) (hG_bdd : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => P)
      {s | ∃ g ∈ G, empRademacherR G s <
        (((∫ u, g u ∂P) - empMean s g
          - 3 * gbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by sorry

end PrescAnalytics.ERM

