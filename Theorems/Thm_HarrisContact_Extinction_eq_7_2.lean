import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- (7.2) (p. 981): with μ = 1 and λ_k = kλ, π₁ = 2dλ/(1 + 2dλ) · π₂ for every site x and
every neighbour y of x. -/
theorem eq_7_2 {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x y : Site d, ∑ i, |x i - y i| = 1 →
      survInf 1 (fun k => (k : ℝ) * l) {x} =
        ENNReal.ofReal (2 * d * l / (1 + 2 * d * l)) * survInf 1 (fun k => (k : ℝ) * l) {x, y} := by sorry

end HarrisContact.Extinction

