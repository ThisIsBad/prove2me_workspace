import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
open scoped ENNReal
theorem lemma3_hitting_sum_growth (M : Model) (U : ℤ) (q : ℕ) (hq : 0 < q) (v : ℤ → ℝ)
    (hv : ∃ A B : ℝ, ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ q)
    (l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U) (hlu : l ≤ u - M.b) :
    ∃ A' B' : ℝ, ∀ x ≤ U,
      H M U l u (fun z => ENNReal.ofReal |v z|) x ≤ ENNReal.ofReal (A' + B' * |(x : ℝ)| ^ (q + 3)) := by sorry
end FedergruenZipkin.AvgCost

