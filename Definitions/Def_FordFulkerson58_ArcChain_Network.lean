import Mathlib

namespace FordFulkerson58.ArcChain

/-- A multi-commodity network (Ford–Fulkerson 1958, §2, pp. 1778–1779, and §3, p. 1780).
Nodes form the type `V` (the page's `P₁, …, P_N`) and arcs the type `E` (the page's `A₁, …, A_m`);
arc `e` joins `tail e` and `head e`. If `directed e = true` the arc may only be traversed from `tail e`
to `head e`; otherwise it is undirected and may be traversed both ways. `b e` is the flow capacity of
`e`. Commodities form the type `ι`; commodity `k` has the set of sources `src k` (`S_k`) and the set of
sinks `snk k` (`T_k`). -/
structure Network (V E ι : Type*) where
  tail : E → V
  head : E → V
  directed : E → Bool
  b : E → ℝ
  src : ι → Finset V
  snk : ι → Finset V

variable {V E ι : Type*}

/-- Arc `e` can be traversed from `u` to `v`: either `e` goes from `u` to `v`, or `e` is undirected and
goes from `v` to `u`. -/
def Traverses (N : Network V E ι) (e : E) (u v : V) : Prop :=
  (N.tail e = u ∧ N.head e = v) ∨ (N.directed e = false ∧ N.tail e = v ∧ N.head e = u)

/-- `IsChainWalk N u w p vs`: the arc list `p` and the node list `vs` arrange a chain from `u` to `w`:
`vs` has one more entry than `p`, starts at `u`, ends at `w`, has no repeated node, `p` has no repeated
arc, and the `i`-th arc can be traversed from the `i`-th to the `(i+1)`-th node. With `p = []` and
`vs = [u]` it is the null chain from `u` to `u`. -/
def IsChainWalk (N : Network V E ι) (u w : V) (p : List E) (vs : List V) : Prop :=
  vs.length = p.length + 1 ∧ vs.head? = some u ∧ vs.getLast? = some w ∧ vs.Nodup ∧ p.Nodup ∧
  ∀ (i : ℕ) (h : i < p.length), ∃ x y : V,
    vs[i]? = some x ∧ vs[i + 1]? = some y ∧ Traverses N p[i] x y

/-- A chain from `u` to `w`: a set `C` of arcs that can be arranged as a chain walk from `u` to `w`. -/
def IsChain [DecidableEq E] (N : Network V E ι) (u w : V) (C : Finset E) : Prop :=
  ∃ (p : List E) (vs : List V), IsChainWalk N u w p vs ∧ p.toFinset = C

/-- A chain from some node of the set `S` to the node `w`. -/
def IsChainFrom [DecidableEq E] (N : Network V E ι) (S : Finset V) (w : V) (C : Finset E) : Prop :=
  ∃ u ∈ S, IsChain N u w C

/-- A chain for commodity `k`: a chain joining a source of `k` with a sink of `k`. -/
def IsCommodityChain [DecidableEq E] (N : Network V E ι) (k : ι) (C : Finset E) : Prop :=
  ∃ t ∈ N.snk k, IsChainFrom N (N.src k) t C

/-- The commodity chains `C₁, …, C_n` of §2, as pairs (commodity, arc set). The same arc set used by two
commodities gives two columns. -/
abbrev Col [DecidableEq E] (N : Network V E ι) : Type _ :=
  {kc : ι × Finset E // IsCommodityChain N kc.1 kc.2}

noncomputable instance instFintypeCol [Fintype ι] [Fintype E] [DecidableEq E] (N : Network V E ι) :
    Fintype (Col N) := by
  classical
  exact Subtype.fintype _

/-- The incidence matrix (1): `a_rs = 1` if the chain `C_s` contains the arc `A_r`, `0` otherwise. -/
def inc [DecidableEq E] (N : Network V E ι) (r : E) (s : Col N) : ℝ :=
  if r ∈ s.1.2 then 1 else 0

end FordFulkerson58.ArcChain
