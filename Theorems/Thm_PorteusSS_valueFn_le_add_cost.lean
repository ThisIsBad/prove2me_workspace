import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 2 (p. 418). If `x ≤ y` and `n ≥ 1`, then `f_n(x) ≤ f_n(y) + c(y - x)`. The hypothesis
`hfin` is the paper's standing convention (§X) that `f_n` is real valued, i.e. that each
infimum in (4) is over a set bounded below. -/
theorem valueFn_le_add_cost (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (n : ℕ) (hn : 1 ≤ n)
    (hfin : ∀ x : ℝ, BddBelow (range fun w : Ici x => c ((w : ℝ) - x) + hFn c m φ f0 α n w))
    (x y : ℝ) (hxy : x ≤ y) :
    valueFn c m φ f0 α n x ≤ valueFn c m φ f0 α n y + c (y - x) := by sorry

end PorteusSS
