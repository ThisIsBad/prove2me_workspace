import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- Theorem 2.5, (2.44), p. 767 (Nagaev–Sakoyan): if `g` has a positive nondecreasing
derivative `g′`, then for any `x > 0`,
`P(S_n ≥ x) ≤ ∏_{j=1}^n (b_j(x/n) + b_gj) · exp{−n g(x/n)}`. -/
theorem theorem_2_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (hbg : ∀ j, IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (x : ℝ) (hx : 0 < x) :
    P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω}
      ≤ (∏ j, (bj P X g g' j (x / n) + bg P X g j)) * Real.exp (-(n * g (x / n))) := by sorry

end NagaevLD.GenMoment

