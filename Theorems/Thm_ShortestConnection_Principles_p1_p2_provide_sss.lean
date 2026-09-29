import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §IV, p. 1396: "P1 and P2 will provide a SSS for any connected labelled graph with
any set of real edge "lengths." The "lengths" need not even be positive, or of the same sign."
For every finite connected graph `G` and every real edge lengths `w`, a complete construction by
P1 and P2 (`N - 1` applications, `N = card V`) exists, and the links of every complete
construction form a shortest spanning subtree of `G`. -/
theorem p1_p2_provide_sss {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) :
    (∃ l : List (Sym2 V), IsCompleteConstruction G w l) ∧
      ∀ l : List (Sym2 V), IsCompleteConstruction G w l → IsSSS G w l.toFinset := by sorry

end ShortestConnection.Principles
