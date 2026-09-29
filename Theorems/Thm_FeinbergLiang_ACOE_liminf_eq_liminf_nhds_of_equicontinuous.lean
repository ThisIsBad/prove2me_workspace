import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Lemma 3.3 (Feinberg–Liang 2022, p. 574). For an equicontinuous family of nonnegative real
functions `f n` on a metric space with `sup_n f n x < ∞` for each `x`,
`liminf_{n → ∞} f n x = liminf_{n → ∞, y → x} f n y`. Both sides are taken in `ℝ≥0∞`
(`ENNReal.ofReal` is exact on the nonnegative values). -/
theorem liminf_eq_liminf_nhds_of_equicontinuous {Y : Type*} [MetricSpace Y] (f : ℕ → Y → ℝ)
    (hf_nonneg : ∀ n y, 0 ≤ f n y) (hf_equi : Equicontinuous f)
    (hf_bdd : ∀ y, BddAbove (Set.range fun n => f n y)) (x : Y) :
    liminf (fun n => ENNReal.ofReal (f n x)) atTop =
      liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2)) (atTop ×ˢ 𝓝 x) := by sorry

end FeinbergLiang.ACOE
