import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- Proof of Theorem 2.5, p. 768, after (2.48): for `h = g′(x/n)`,
`E e^{hX_j} ≤ (b_j(x/n) + b_gj) exp{hx/n − g(x/n)}`. -/
theorem per_factor_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j))
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0)) (j : Fin n)
    (hbg : IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    ∫ ω, Real.exp (h * X j ω) ∂P
      ≤ (bj P X g g' j (x / n) + bg P X g j) * Real.exp (h * (x / n) - g (x / n)) := by sorry

end NagaevLD.GenMoment

