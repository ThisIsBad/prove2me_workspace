import Mathlib

namespace SendSplit.Existence

/-- A directed graph `G = (N, A)` on the node set `N = Fin n`: a finite set `A` of ordered pairs
of distinct nodes, called arcs (Erickson–Monma–Veinott 1987, p. 638). -/
structure ArcGraph (n : ℕ) where
  /-- The arcs. -/
  A : Finset (Fin n × Fin n)
  /-- Arcs join distinct nodes. -/
  loopless : ∀ p ∈ A, p.1 ≠ p.2

variable {n : ℕ}

/-- A preflow: a nonnegative matrix `x = (x i j)` carried by the arcs (zero off `A`). -/
def IsPreflow (G : ArcGraph n) (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ ∀ i j, (i, j) ∉ G.A → x i j = 0

/-- A flow for the demand vector `r`: a preflow with inflow minus outflow equal to `r i`
at every node `i`. -/
def IsFlow (G : ArcGraph n) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) : Prop :=
  IsPreflow G x ∧
    ∀ i, (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), x j i)
        - (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), x i k) = r i

/-- A circulation: a flow for the zero demand vector. -/
def IsCirculation (G : ArcGraph n) (x : Fin n → Fin n → ℝ) : Prop :=
  IsFlow G (fun _ => 0) x

/-- The additive flow cost `c(x) = ∑_{(i,j) ∈ A} c_ij(x_ij)`. -/
def flowCost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ p ∈ G.A, c p.1 p.2 (x p.1 p.2)

/-- The standing assumptions on the arc costs: each `c_ij` is concave on `[0, ∞)` and
`c_ij(0) = 0`. -/
def IsConcaveArcCost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) : Prop :=
  ∀ p ∈ G.A, ConcaveOn ℝ (Set.Ici 0) (c p.1 p.2) ∧ c p.1 p.2 0 = 0

/-- A minimum-cost flow for `r`: a flow for `r` whose cost is at most that of every flow
for `r`. -/
def IsMinCostFlow (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (x : Fin n → Fin n → ℝ) : Prop :=
  IsFlow G r x ∧ ∀ x', IsFlow G r x' → flowCost G c x ≤ flowCost G c x'

/-- The arcs of the subgraph induced by a preflow: the arcs carrying nonzero flow. -/
noncomputable def support (G : ArcGraph n) (x : Fin n → Fin n → ℝ) : Finset (Fin n × Fin n) :=
  G.A.filter (fun p => x p.1 p.2 ≠ 0)

/-- A set `F` of arcs is a forest (in the undirected sense, over arcs): there is no undirected
cycle, i.e. no cyclic sequence of `m + 2 ≥ 2` distinct nodes `v 0, …, v (m+1)` and distinct arcs
`e 0, …, e (m+1)` of `F` such that each `e k` joins `v k` and `v (k+1)` (indices mod `m + 2`) in
either direction. A pair of antiparallel arcs `(i, j), (j, i)` in `F` is a cycle of length 2. -/
def IsForest (F : Finset (Fin n × Fin n)) : Prop :=
  ¬ ∃ (m : ℕ) (v : Fin (m + 2) → Fin n) (e : Fin (m + 2) → Fin n × Fin n),
    Function.Injective v ∧ Function.Injective e ∧
      ∀ k, e k ∈ F ∧ (e k = (v k, v (k + 1)) ∨ e k = (v (k + 1), v k))

/-- An extreme flow for `r`: a flow for `r` whose induced subgraph is a forest. -/
def IsExtremeFlow (G : ArcGraph n) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) : Prop :=
  IsFlow G r x ∧ IsForest (support G x)

/-- `C` is the arc set of a simple circuit of `G`: there are `m + 2 ≥ 2` distinct nodes
`v 0, …, v (m+1)` with every `(v k, v (k+1))` an arc (indices mod `m + 2`), and `C` is the set
of these arcs. -/
def IsSimpleCircuit (G : ArcGraph n) (C : Finset (Fin n × Fin n)) : Prop :=
  ∃ (m : ℕ) (v : Fin (m + 2) → Fin n), Function.Injective v ∧
    (∀ k, (v k, v (k + 1)) ∈ G.A) ∧ C = Finset.univ.image (fun k => (v k, v (k + 1)))

/-- A simple circulation (extreme direction-of-recession): a circulation whose induced
subgraph is a simple circuit. -/
def IsSimpleCirculation (G : ArcGraph n) (y : Fin n → Fin n → ℝ) : Prop :=
  IsCirculation G y ∧ IsSimpleCircuit G (support G y)

end SendSplit.Existence
