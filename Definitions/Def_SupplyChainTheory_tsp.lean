import Mathlib

open Classical

namespace SupplyChainTheory

/-! ### Tours and the metric TSP, Sect. 10.2 -/

/-- Symmetric nonnegative distances with `cᵢᵢ = 0` satisfying the triangle inequality (10.1). -/
structure IsMetric {n : ℕ} (c : Fin n → Fin n → ℝ) : Prop where
  symm : ∀ i j, c i j = c j i
  nonneg : ∀ i j, 0 ≤ c i j
  refl : ∀ i, c i i = 0
  triangle : ∀ i j k, c i j ≤ c i k + c k j

/-- A tour is a visiting order `τ 0, τ 1, …, τ (n−1)`, returning to `τ 0`; its length is
`z(Γ) = ∑ₖ c(τ k, τ (k+1))`, indices mod `n`. -/
def tourLength {n : ℕ} (c : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k, c (τ k) (τ (finRotate n k))

/-- `z*`, the length of an optimal tour. -/
noncomputable def optTourLength {n : ℕ} (c : Fin n → Fin n → ℝ) : ℝ :=
  sInf (Set.range (tourLength c))

/-- The edges `{τ k, τ (k+1)}` of a tour. -/
def tourEdges {n : ℕ} (τ : Equiv.Perm (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image (fun k => s(τ k, τ (finRotate n k)))

/-- The cost of an undirected edge, `(cᵢⱼ + cⱼᵢ)/2`, which is `cᵢⱼ` for symmetric `c`. -/
noncomputable def edgeCost {n : ℕ} (c : Fin n → Fin n → ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j => (c i j + c j i) / 2, fun i j => by dsimp only; rw [add_comm]⟩

/-- `z(E)`, the total length of a set of edges. -/
noncomputable def edgeSetWeight {n : ℕ} (c : Fin n → Fin n → ℝ) (E : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ e ∈ E, edgeCost c e

/-- The number of tour edges with both ends in `S`, `∑_{i,j ∈ S} xᵢⱼ`. -/
def edgesWithin {n : ℕ} (τ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ((tourEdges τ).filter (fun e => ∀ v ∈ e, v ∈ S)).card

/-- The number of tour edges with exactly one end in `S`, `∑_{i ∈ S, j ∉ S} xᵢⱼ`. -/
def edgesLeaving {n : ℕ} (τ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ((tourEdges τ).filter (fun e => ∃ v ∈ e, v ∈ S ∧ ∃ w ∈ e, w ∉ S)).card

/-- Handle `H` and teeth `T₁, …, Tₛ` of a comb (Theorem 10.4): each tooth meets `H` and its
complement, the teeth are pairwise disjoint, and `s ≥ 3` is odd. -/
def IsComb {n s : ℕ} (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) : Prop :=
  (∀ k, (∃ v ∈ T k, v ∈ H) ∧ ∃ v ∈ T k, v ∉ H) ∧ (∀ k l, k ≠ l → Disjoint (T k) (T l))
    ∧ 3 ≤ s ∧ Odd s

/-! ### Reduced distance matrices, Sect. 10.3.2 -/

/-- The reduced matrix `c'ᵢⱼ = cᵢⱼ − ρᵢ − κⱼ` of Little et al., applied to every entry `i ≠ j`. -/
def reducedCost {n : ℕ} (c : Fin n → Fin n → ℝ) (ρ κ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  c i j - ρ i - κ j

/-! ### Construction heuristics, Sect. 10.4 -/

/-- A nearest-neighbor tour (Algorithm 10.1): each node visited is a nearest unvisited node. -/
def IsNearestNeighborTour {n : ℕ} (c : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k j : Fin n, k.val + 1 < n → (∀ l, l ≤ k → τ l ≠ j) →
    c (τ k) (τ (finRotate n k)) ≤ c (τ k) j

/-- The length of the closed tour through the nodes of a list in order (a one-node list has
length `0`, a two-node list `2 c_{ab}`). -/
def cycleLength {n : ℕ} (c : Fin n → Fin n → ℝ) (L : List (Fin n)) : ℝ :=
  (List.zipWith c L (L.rotate 1)).sum

/-- The distance from a node to a partial tour, `min_{m ∈ L} c_{m k}` (Algorithm 10.2, line 4). -/
noncomputable def distToTour {n : ℕ} (c : Fin n → Fin n → ℝ) (L : List (Fin n)) (k : Fin n) : ℝ :=
  sInf ((fun m => c m k) '' {m | m ∈ L})

/-- A run of the nearest insertion heuristic (Algorithm 10.2): partial tours `L 0 = [i₀]`,
`L 1`, …, each obtained from the previous one by inserting an unvisited node nearest to the tour
at a position that minimises the resulting tour length. -/
def IsNearestInsertionRun {n : ℕ} (c : Fin n → Fin n → ℝ) (L : ℕ → List (Fin n)) : Prop :=
  (∃ i₀, L 0 = [i₀]) ∧ ∀ k, k + 1 < n → ∃ (x : Fin n) (pos : ℕ), x ∉ L k
    ∧ (∀ y, y ∉ L k → distToTour c (L k) x ≤ distToTour c (L k) y)
    ∧ pos ≤ (L k).length ∧ L (k + 1) = (L k).insertIdx pos x
    ∧ ∀ pos', pos' ≤ (L k).length →
        cycleLength c (L (k + 1)) ≤ cycleLength c ((L k).insertIdx pos' x)

/-! ### Spanning trees, Eulerian walks and shortcutting, Sect. 10.4.6-10.4.7 -/

/-- The total length of the edges of a graph on the nodes. -/
noncomputable def graphWeight {n : ℕ} (c : Fin n → Fin n → ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ e ∈ G.edgeFinset, edgeCost c e

/-- A minimum spanning tree: a spanning tree of least total length. -/
def IsMST {n : ℕ} (c : Fin n → Fin n → ℝ) (T : SimpleGraph (Fin n)) : Prop :=
  T.IsTree ∧ ∀ T' : SimpleGraph (Fin n), T'.IsTree → graphWeight c T ≤ graphWeight c T'

/-- `τ` visits the nodes in the order of their first appearance along the node list `l`
(shortcutting: "visiting nodes in the same sequence but skipping duplicates"). -/
def IsShortcut {n : ℕ} (l : List (Fin n)) (τ : Equiv.Perm (Fin n)) : Prop :=
  (∀ v, v ∈ l) ∧ ∀ a b, τ.symm a < τ.symm b ↔ l.idxOf a < l.idxOf b

/-- The odd-degree nodes of a graph. -/
noncomputable def oddNodes {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => Odd (G.degree v))

/-- `M` is a perfect matching on the node set `O`: disjoint edges, each with both ends in `O`,
covering every node of `O` exactly once. -/
def IsPerfectMatchingOn {n : ℕ} (O : Finset (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ O) ∧ ∀ v ∈ O, ∃! e, e ∈ M ∧ v ∈ e

/-- A minimum-weight perfect matching on `O`. -/
def IsMinMatchingOn {n : ℕ} (c : Fin n → Fin n → ℝ) (O : Finset (Fin n))
    (M : Finset (Sym2 (Fin n))) : Prop :=
  IsPerfectMatchingOn O M ∧ ∀ M', IsPerfectMatchingOn O M' → edgeSetWeight c M ≤ edgeSetWeight c M'

/-! ### 1-trees and the Held-Karp bound, Sect. 10.6.1 -/

/-- A 1-tree (Held and Karp) rooted at the node `r` (the book's node 1): a spanning tree on the
other nodes plus two edges incident to `r`. -/
def Is1Tree {n : ℕ} (r : Fin n) (G : SimpleGraph (Fin n)) : Prop :=
  (G.induce {v : Fin n | v ≠ r}).IsTree ∧ G.degree r = 2

/-- The least length of a 1-tree rooted at `r`. -/
noncomputable def opt1TreeLength {n : ℕ} (c : Fin n → Fin n → ℝ) (r : Fin n) : ℝ :=
  sInf {w | ∃ G : SimpleGraph (Fin n), Is1Tree r G ∧ w = graphWeight c G}

/-- (10.31): the revised distances `c'ᵢⱼ = cᵢⱼ + λᵢ + λⱼ`. -/
def revisedCost {n : ℕ} (c : Fin n → Fin n → ℝ) (lam : Fin n → ℝ) (i j : Fin n) : ℝ :=
  c i j + lam i + lam j
end SupplyChainTheory
