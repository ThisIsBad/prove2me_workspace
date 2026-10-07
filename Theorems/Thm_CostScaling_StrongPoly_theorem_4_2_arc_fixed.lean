import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Theorem 4.2, p. 16: an arc with a sufficiently large absolute reduced cost
has the same flow in a given `ε`-optimal circulation and every `ε'`-optimal
circulation. The paper's standing `m ≥ n - 1 ≥ 1` is explicit. -/
theorem theorem_4_2_arc_fixed (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (v w : V) (hvw : (v, w) ∈ N.E)
    (hcost : (Fintype.card V : ℝ) * (ε + ε') ≤ |reducedCost N p v w|) :
    ∀ f' : V → V → ℝ, IsEpsOptimal N f' ε' → f v w = f' v w := by sorry

end CostScaling.StrongPoly

