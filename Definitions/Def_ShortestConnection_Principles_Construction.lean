import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree

namespace ShortestConnection.Principles

/-- One application of Principle 1 (Prim 1957, p. 1391: "Any isolated terminal can be connected
to a nearest neighbor") to the links `F` made so far, adding the link `e`.
The terminal `t` is isolated (no link of `F` meets it), and `e = s(t, n)` joins `t` to a nearest
neighbor `n`: `t–n` is an edge of `G` and `w s(t, n) ≤ w s(t, m)` for every `G`-neighbor `m` of `t`.
Only edges of `G` count as possible links (a missing edge has length `∞`, p. 1399). -/
def IsP1Step {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (e : Sym2 V) : Prop :=
  ∃ t n : V, (∀ x : V, ¬ (linkGraph F).Adj t x) ∧ G.Adj t n ∧ e = s(t, n) ∧
    ∀ m : V, G.Adj t m → w s(t, n) ≤ w s(t, m)

/-- One application of Principle 2 (Prim 1957, p. 1391: "Any isolated fragment can be connected to
a nearest neighbor by a shortest available link") to the links `F` made so far, adding `e`.
The isolated fragment is the connected component `C = {x | (linkGraph F).Reachable u x}` of a
terminal `u` that has at least one link (so `C` has at least two terminals; an isolated fragment
has no external connections, so it is a whole component). The link `e = s(u, n)` is an edge of
`G` with `n ∉ C`, and it is no longer than any edge `s(u', n')` of `G` with `u' ∈ C`, `n' ∉ C`.
Since the distance of `n` from `C` is the least length of a `G`-edge from `n` into `C`, this single
inequality says exactly that `n` is a nearest neighbor of `C` and `u–n` a shortest link from `n`
to `C`. -/
def IsP2Step {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (e : Sym2 V) : Prop :=
  ∃ u n : V, (∃ x : V, (linkGraph F).Adj u x) ∧ ¬ (linkGraph F).Reachable u n ∧ G.Adj u n ∧
    e = s(u, n) ∧
    ∀ u' n' : V, (linkGraph F).Reachable u u' → ¬ (linkGraph F).Reachable u n' → G.Adj u' n' →
      w s(u, n) ≤ w s(u', n')

/-- An application of P1 or P2 to the links `F` made so far, adding the link `e`
(Prim 1957, pp. 1391–1392; P1 and P2 may be applied to any isolated terminal or fragment, in any
order). -/
def IsApplication {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (e : Sym2 V) : Prop :=
  IsP1Step G w F e ∨ IsP2Step G w F e

/-- A construction by P1 and P2 (Prim 1957, §II): a list of links in which each link is an
application of P1 or P2 with respect to the links chosen before it. -/
def IsConstruction {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (l : List (Sym2 V)) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), IsApplication G w (l.take i).toFinset l[i]

/-- A complete construction by P1 and P2: a construction with `N - 1` links, where `N` is the
number of terminals (Prim 1957, p. 1392: "an N-terminal network is connected by N-1
applications"). `Fintype.card V - 1` is natural-number subtraction; it is used only for nonempty
`V`. -/
def IsCompleteConstruction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (l : List (Sym2 V)) : Prop :=
  IsConstruction G w l ∧ l.length = Fintype.card V - 1

end ShortestConnection.Principles
