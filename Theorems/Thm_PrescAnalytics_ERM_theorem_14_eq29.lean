import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic

namespace PrescAnalytics.ERM

open MeasureTheory

/-- Theorem 14, (29) (p. 40), with the corrected boundedness `0 ≤ g ≤ ḡ`. Let `G` be a pointwise
separable class of measurable functions `U → ℝ` with values in `[0, ḡ]`, `P` a probability measure on
`U`, `N ≥ 1`, `δ > 0`. Outside a set of `P^N`-measure at most `δ`, every sample
`S_N = (u^1, …, u^N)` satisfies
`E[g(T)] ≤ (1/N) Σ_i g(u^i) + ḡ √(log(1/δ)/(2N)) + ℜ_N(G)` for all `g ∈ G` simultaneously
(stated as: the bad set, an outer measure, is `≤ δ`; the inequality is written
`ofReal(E g − Ê g − ḡ√…) ≤ ℜ_N(G)`, equivalent since `ℜ_N(G) ≥ 0`). -/
theorem theorem_14_eq29 {U : Type*} [MeasurableSpace U] (P : Measure U) [IsProbabilityMeasure P]
    (G : Set (U → ℝ)) (gbar : ℝ) (hG_meas : ∀ g ∈ G, Measurable g)
    (hG_sep : IsPointwiseSeparable G) (hG_bdd : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => P)
      {s | ∃ g ∈ G, margRademacherR P N G <
        ENNReal.ofReal ((∫ u, g u ∂P) - empMean s g
          - gbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} ≤ ENNReal.ofReal δ := by sorry

end PrescAnalytics.ERM

