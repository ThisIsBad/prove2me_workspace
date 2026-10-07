import Mathlib

namespace ChinesePostman.NextNode

/-! Edmonds and Johnson (1973), §2, p. 89 (graphs, tours) and §5, pp. 109–112
(next-node representation of a tour, Theorem 5.1's conditions, the §5.2 next-node algorithm). -/

/-- A graph in §2, p. 89: finite node and edge types, two distinct ends for each edge,
and separate edge identities for parallel edges. Finiteness is supplied at each use. -/
structure Graph (V E : Type) where
  ends : E → Sym2 V
  loopless : ∀ e, ¬ (ends e).IsDiag

/-- The degree of a node: the number of edges meeting it, parallel edges counted separately. -/
def degree {V E : Type} [Fintype E] [DecidableEq V] (G : Graph V E) (n : V) : ℕ :=
  (Finset.univ.filter (fun e => n ∈ G.ends e)).card

/-- The number of edges meeting both nodes `n` and `m`. -/
def edgeCount {V E : Type} [Fintype E] [DecidableEq V] (G : Graph V E) (n m : V) : ℕ :=
  (Finset.univ.filter (fun e => G.ends e = s(n, m))).card

/-- An alternating sequence `(n₁, e₁, n₂, …, e_l, n_{l+1})` with `e_i` meeting `n_i` and
`n_{i+1}`; the one-node sequence (`l = 0`) is allowed. -/
def IsWalk {V E : Type} (G : Graph V E) (ns : List V) (es : List E) : Prop :=
  ∃ hlen : ns.length = es.length + 1,
    ∀ (i : ℕ) (h : i < es.length),
      G.ends es[i] = s(ns[i]'(by omega), ns[i + 1]'(by omega))

/-- A tour: a walk with `n_{l+1} = n₁`. -/
def IsTour {V E : Type} (G : Graph V E) (ns : List V) (es : List E) : Prop :=
  IsWalk G ns es ∧ ns.head? = ns.getLast?

/-- An Euler tour: a tour containing every edge exactly once. -/
def IsEulerTour {V E : Type} [DecidableEq E] (G : Graph V E) (ns : List V) (es : List E) :
    Prop :=
  IsTour G ns es ∧ ∀ e : E, es.count e = 1

/-- `G` is connected: every two nodes are joined by a walk. -/
def Connected {V E : Type} (G : Graph V E) : Prop :=
  ∀ u v : V, ∃ (ns : List V) (es : List E),
    IsWalk G ns es ∧ ns.head? = some u ∧ ns.getLast? = some v

/-- One step of following next-node lists `L` (§5, p. 109). The state is the current node `u`
and the number `t n` of departures already made from each node `n`. With `k = (L u).length`,
the paper's `L_u(i)` is `(L u)[i - 1]`; the `(t u + 1)`-st departure from `u` goes to
`L_u(k - t u)`, i.e. the lists are read from the last entry to the first. If every entry of
`L u` has been used, the traversal stops (`none`). -/
def nextState {V : Type} [DecidableEq V] (L : V → List V) (u : V) (t : V → ℕ) :
    Option (V × (V → ℕ)) :=
  if h : t u < (L u).length then
    some ((L u)[(L u).length - 1 - t u]'(by omega), Function.update t u (t u + 1))
  else none

/-- Follow the lists for at most `fuel` steps from node `u` with departure counters `t`;
returns the sequence of nodes visited (starting with `u`) and the final counters. -/
def followAux {V : Type} [DecidableEq V] (L : V → List V) :
    ℕ → V → (V → ℕ) → List V × (V → ℕ)
  | 0, u, t => ([u], t)
  | fuel + 1, u, t =>
    match nextState L u t with
    | none => ([u], t)
    | some (v, t') =>
      let p := followAux L fuel v t'
      (u :: p.1, p.2)

/-- The total number of list entries, `∑_n k_n`. -/
def totalEntries {V : Type} [Fintype V] (L : V → List V) : ℕ :=
  ∑ n, (L n).length

/-- The tour specified by next-node lists `L` and starting node `r` (§5, p. 109; §5.2, p. 111):
start at `r` with no departures made (the start is `r`'s first visit, so the first departure is
to `L_r(k_r)`), leave each node `n` the `j`-th time it is reached by going to `L_n(k_n - j + 1)`,
and stop at the first node whose list is used up. Each step uses one list entry, so
`totalEntries L` steps suffice for the traversal to stop. Returns the node sequence and the
final departure counters. -/
def follow {V : Type} [Fintype V] [DecidableEq V] (L : V → List V) (r : V) :
    List V × (V → ℕ) :=
  followAux L (totalEntries L) r (fun _ => 0)

/-- The entries of `L n` not yet used when `t n` departures from `n` have been made: since the
lists are read backwards, these are `L_n(1), …, L_n(k_n - t n)`. -/
def unused {V : Type} (L : V → List V) (t : V → ℕ) (n : V) : List V :=
  (L n).take ((L n).length - t n)

/-- Next-node lists `L` with starting node `r` describe an Euler tour of `G`: following them from
`r` uses every entry of every list, and the node sequence of the traversal is the node sequence of
an Euler tour of `G` (for some choice of the edge traversed at each step). -/
def DescribesEulerTour {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : Graph V E) (r : V) (L : V → List V) : Prop :=
  (∀ n, (follow L r).2 n = (L n).length) ∧ ∃ es : List E, IsEulerTour G (follow L r).1 es

/-- Theorem 5.1 (i): every list has length `k_n` equal to one half of the degree of `n`. -/
def CondI {V E : Type} [Fintype E] [DecidableEq V] (G : Graph V E) (L : V → List V) : Prop :=
  ∀ n, 2 * (L n).length = degree G n

/-- Theorem 5.1 (ii): for all nodes `n, m`, the number of edges meeting both `n` and `m` equals
the number of times `n = L_m(i)` plus the number of times `m = L_n(i)`. -/
def CondII {V E : Type} [Fintype E] [DecidableEq V] (G : Graph V E) (L : V → List V) : Prop :=
  ∀ n m, edgeCount G n m = (L m).count n + (L n).count m

/-- The parent map of the last-exit edges: `n ↦ L_n(1)` for `n ≠ r` (the first entry of the list,
`n` itself if the list is empty), and `r ↦ r`. -/
def parent {V : Type} [DecidableEq V] (r : V) (L : V → List V) (u : V) : V :=
  if u = r then r else (L u).headD u

/-- Theorem 5.1 (iii), stated for the edges `(n, L_n(1))`, `n ≠ r` (see the Formalization Note):
every node `n ≠ r` has a nonempty list and an edge of `G` to `L_n(1)`, and following the edges `n → L_n(1)` from any node leads
to `r`, so these `|V| - 1` directed edges form an arborescence with root `r`. -/
def CondIII {V E : Type} [DecidableEq V] (G : Graph V E) (r : V) (L : V → List V) : Prop :=
  (∀ n, n ≠ r → L n ≠ []) ∧
  (∀ n, n ≠ r → ∃ e : E, G.ends e = s(n, (L n).headD n)) ∧
  ∀ n, ∃ j : ℕ, (parent r L)^[j] n = r

/-! The next-node algorithm (§5.2, p. 111). -/

/-- A state of the next-node algorithm: either about to execute Step 1 with the current values of
`n₀`, `n`, the edge `e`, the set of used edges and the lists, or terminated with the lists. -/
inductive AlgState (V E : Type) where
  | step1 (n₀ n : V) (e : E) (used : Finset E) (L : V → List V)
  | done (L : V → List V)

/-- One pass of the algorithm from Step 1 to the next Step 1 (through Step 2 or Step 3) or to
termination. In Step 1, `m` is the node other than `n` meeting `e`; `k_m` is increased by one and
the new entry `L_m(k_m) = n` is appended at the end of `L m`; `e` becomes used. Then:
Step 2 if `m` meets an unused edge (any such edge may be chosen), otherwise Step 3: any node `n₀`
meeting a used and an unused edge `e` may be chosen, or the algorithm terminates if there is none.
-/
inductive AlgStep {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E) :
    AlgState V E → AlgState V E → Prop
  | step2 (n₀ n m : V) (e e' : E) (used : Finset E) (L : V → List V)
      (hm : G.ends e = s(n, m)) (he' : e' ∉ insert e used) (hme' : m ∈ G.ends e') :
      AlgStep G (.step1 n₀ n e used L)
        (.step1 n₀ m e' (insert e used) (Function.update L m (L m ++ [n])))
  | step3 (n₀ n m n₀' : V) (e e' : E) (used : Finset E) (L : V → List V)
      (hm : G.ends e = s(n, m))
      (hstuck : ∀ f, m ∈ G.ends f → f ∈ insert e used)
      (hused : ∃ f ∈ insert e used, n₀' ∈ G.ends f)
      (he' : e' ∉ insert e used) (hn₀e' : n₀' ∈ G.ends e') :
      AlgStep G (.step1 n₀ n e used L)
        (.step1 n₀' n₀' e' (insert e used) (Function.update L m (L m ++ [n])))
  | stop (n₀ n m : V) (e : E) (used : Finset E) (L : V → List V)
      (hm : G.ends e = s(n, m))
      (hstuck : ∀ f, m ∈ G.ends f → f ∈ insert e used)
      (hnone : ∀ v, (∃ f ∈ insert e used, v ∈ G.ends f) → ∀ f, v ∈ G.ends f → f ∈ insert e used) :
      AlgStep G (.step1 n₀ n e used L) (.done (Function.update L m (L m ++ [n])))

/-- The lists `L` are produced by a complete run of the next-node algorithm started (Step 0) at
node `r` with edge `e₀` meeting `r`: all `k_i = 0` (empty lists), `n₀ = n = r`, no edge used,
and some sequence of steps reaches termination with lists `L`. -/
def AlgProduces {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E) (r : V) (e₀ : E)
    (L : V → List V) : Prop :=
  Relation.ReflTransGen (AlgStep G) (.step1 r r e₀ ∅ (fun _ => [])) (.done L)

end ChinesePostman.NextNode
