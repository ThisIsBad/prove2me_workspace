import Mathlib

namespace SendSplit.DPEquations

/-- Section 2 (p. 638): a (directed) graph `G = (N, A)` on the nodes `N = Fin n` whose arcs
`A` are ordered pairs of *distinct* nodes. -/
def IsGraph {n : ℕ} (A : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ A, p.1 ≠ p.2

/-- A preflow is a nonnegative matrix `x = (x_ij)`; it carries flow only on arcs of `A`. -/
def IsPreflow {n : ℕ} (A : Finset (Fin n × Fin n)) (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ ∀ i j, (i, j) ∉ A → x i j = 0

/-- A flow for the demand vector `r` is a preflow satisfying conservation of flow:
inflow minus outflow at node `i` equals the demand `r i`, for every node `i`. -/
def IsFlow {n : ℕ} (A : Finset (Fin n × Fin n)) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) :
    Prop :=
  IsPreflow A x ∧
    ∀ i : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ A), x j i)
        - (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ A), x i k) = r i

/-- Standing assumption on the arc costs (p. 638): each `c_ij` is concave on the nonnegative
half-line and `c_ij(0) = 0` ("without loss of generality and without further mention"). -/
def IsConcaveArcCost {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ) :
    Prop :=
  ∀ p ∈ A, ConcaveOn ℝ (Set.Ici 0) (c p.1 p.2) ∧ c p.1 p.2 0 = 0

/-- The additive flow cost `c(x) = Σ_{(i,j) ∈ A} c_ij(x_ij)`. -/
def flowCost {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ p ∈ A, c p.1 p.2 (x p.1 p.2)

/-- A minimum-cost flow for the demand vector `r`: a flow whose cost is at most the cost of
every flow for `r`. -/
def IsMinCostFlow {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) : Prop :=
  IsFlow A r x ∧ ∀ y, IsFlow A r y → flowCost A c x ≤ flowCost A c y

/-- A simple circulation (p. 638): a circulation whose induced subgraph is a simple circuit,
i.e. there are `m ≥ 2` distinct nodes `v 0, …, v (m-1)` with arcs
`(v k, v (k+1 mod m)) ∈ A`, and the matrix equals a common value `θ > 0` on these arcs and
`0` elsewhere. -/
def IsSimpleCirculation {n : ℕ} (A : Finset (Fin n × Fin n)) (y : Fin n → Fin n → ℝ) :
    Prop :=
  ∃ (m : ℕ) (v : Fin m → Fin n) (θ : ℝ), 2 ≤ m ∧ Function.Injective v ∧ 0 < θ ∧
    (∀ k : Fin m, (v k, v (finRotate m k)) ∈ A) ∧
    ∀ i j, y i j = if ∃ k : Fin m, v k = i ∧ v (finRotate m k) = j then θ else 0

end SendSplit.DPEquations
