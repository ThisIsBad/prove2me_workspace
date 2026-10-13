import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- (7.4) (p. 981): with μ = 1 and λ_k = kλ, for a pair of neighbours ξ = {x, y},
π₂ − π₁ = (1 + (2d − 1)λ) Σ'_{z ∼ ξ} r(ξ, ξ ∪ z)(p_∞(ξ ∪ z) − π₂) ≤ (π₂ − π₁)(2d − 1)λ. -/
theorem eq_7_4 {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x y : Site d, ∑ i, |x i - y i| = 1 →
      (survInf 1 (fun k => (k : ℝ) * l) {x, y}).toReal
          - (survInf 1 (fun k => (k : ℝ) * l) {x}).toReal =
        (1 + (2 * (d : ℝ) - 1) * l) *
          ∑ z ∈ bdry ({x, y} : Config d),
            jump 1 (fun k => (k : ℝ) * l) {x, y} (insert z {x, y}) *
              ((survInf 1 (fun k => (k : ℝ) * l) (insert z {x, y})).toReal
                - (survInf 1 (fun k => (k : ℝ) * l) {x, y}).toReal) ∧
      (survInf 1 (fun k => (k : ℝ) * l) {x, y}).toReal
          - (survInf 1 (fun k => (k : ℝ) * l) {x}).toReal ≤
        ((survInf 1 (fun k => (k : ℝ) * l) {x, y}).toReal
          - (survInf 1 (fun k => (k : ℝ) * l) {x}).toReal) * ((2 * (d : ℝ) - 1) * l) := by sorry

end HarrisContact.Extinction

