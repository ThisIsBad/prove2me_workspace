import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
open scoped ENNReal
theorem corollary1_hitting_sums (M : Model) (U l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U)
    (hlu : l ≤ u - M.b) :
    (∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun _ => (1 : ℝ≥0∞)) x ≤ ENNReal.ofReal (A + B * |(x : ℝ)| ^ 3)) ∧
    (∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≤
        ENNReal.ofReal (A + B * |(x : ℝ)| ^ (M.ρ + 3))) ∧
    ∀ x ≤ U, H M U l u (fun _ => (1 : ℝ≥0∞)) x ≠ ⊤ ∧
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≠ ⊤ := by sorry
end FedergruenZipkin.AvgCost

