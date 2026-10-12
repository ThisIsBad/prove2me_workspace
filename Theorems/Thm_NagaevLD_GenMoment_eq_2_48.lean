import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- (2.48), p. 768: for `h = g′(x/n)`,
`E[e^{hX_j}; X_j < 0] ≤ exp{g(0) + hx/n − g(x/n)} · E[e^{hX_j}; X_j < 0]`. -/
theorem eq_2_48 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j))
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0)) (j : Fin n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    ∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P
      ≤ Real.exp (g 0 + h * (x / n) - g (x / n))
          * ∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P := by sorry

end NagaevLD.GenMoment

