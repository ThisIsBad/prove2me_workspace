import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree
import Definitions.Def_ShortestConnection_Principles_Construction

namespace ShortestConnection.Principles

/-- Necessary Condition 1 (Prim 1957, p. 1392): every terminal in a shortest spanning subtree
`F` of the connected labelled graph `G` is directly connected to at least one nearest neighbor:
for every terminal `t` there is a `G`-neighbor `n` of `t` with `s(t, n) ∈ F` and
`w s(t, n) ≤ w s(t, m)` for every `G`-neighbor `m` of `t`. Lengths are arbitrary reals, ties are
allowed.
Implicit hypotheses made explicit: `G` is connected, and `V` has at least two terminals
(`Nontrivial V`), so that a nearest neighbor exists. -/
theorem necessary_condition_1 {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.Connected) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (hF : IsSSS G w F) (t : V) :
    ∃ n : V, G.Adj t n ∧ s(t, n) ∈ F ∧ ∀ m : V, G.Adj t m → w s(t, n) ≤ w s(t, m) := by sorry

end ShortestConnection.Principles
