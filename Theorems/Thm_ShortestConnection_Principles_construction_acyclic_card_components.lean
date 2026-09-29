import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Prim 1957, §II, p. 1392 ("each application of either P1 or P2 reduces the total number of
isolated terminals and fragments by one"): after the links of any construction by P1 and P2 have
been made, the links form no closed loop, and the number of connected components (isolated
terminals and isolated fragments) is the number of terminals minus the number of links made.
No hypothesis on `G` or on the lengths is needed. -/
theorem construction_acyclic_card_components {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (l : List (Sym2 V)) (hl : IsConstruction G w l) :
    (linkGraph l.toFinset).IsAcyclic ∧
      Nat.card (linkGraph l.toFinset).ConnectedComponent = Fintype.card V - l.length := by sorry

end ShortestConnection.Principles
