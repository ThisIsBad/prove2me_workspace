import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- §7, last sentence of the proof of Theorem 7.1 (p. 981): with μ = 1 and λ_k = kλ,
(2d − 1)λ ≥ 1 if π₁ > 0. -/
theorem pi1_pos_imp {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x : Site d, 0 < survInf 1 (fun k => (k : ℝ) * l) {x} → 1 ≤ (2 * (d : ℝ) - 1) * l := by sorry

end HarrisContact.Extinction

