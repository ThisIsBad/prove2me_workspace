import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), (7.7), p. 982: for `μ = 1`, `λ_k = kλ`, and a pair of neighbours
`ξ = {x, y}`, the first-jump decomposition
`m_2(t) = 2e^{−Kt} + K ∫_0^t e^{−Ks} {(2/K) m_1(t − s) + Σ'_{z ∼ ξ} r(ξ, ξ ∪ z) m_{t−s}(ξ ∪ z)} ds`
with `K = 2 + (4d − 2)λ`. The page's summation variable `x` is renamed `z`. -/
theorem eq_7_7 {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) (x y : HarrisContact.Extinction.Site d) (hxy : y ∈ HarrisContact.Extinction.nbrs x)
    (t : ℝ) (ht : 0 ≤ t) :
    HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) t ({x, y} : HarrisContact.Extinction.Config d) =
      2 * ENNReal.ofReal (Real.exp (-((2 + (4 * (d : ℝ) - 2) * l) * t))) +
      ∫⁻ s in Set.Icc 0 t,
        ENNReal.ofReal ((2 + (4 * (d : ℝ) - 2) * l) * Real.exp (-((2 + (4 * (d : ℝ) - 2) * l) * s))) *
          (ENNReal.ofReal (2 / (2 + (4 * (d : ℝ) - 2) * l)) *
              HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) (t - s) {x} +
            ∑ z ∈ HarrisContact.Extinction.bdry ({x, y} : HarrisContact.Extinction.Config d),
              ENNReal.ofReal (HarrisContact.Extinction.jump 1 (fun k => (k : ℝ) * l) {x, y} (insert z {x, y})) *
                HarrisContact.Extinction.meanSize 1 (fun k => (k : ℝ) * l) (t - s) (insert z {x, y})) := by sorry
end HarrisContact.MeanSize

