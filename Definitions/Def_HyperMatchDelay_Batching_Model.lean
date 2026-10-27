import Mathlib

namespace HyperMatchDelay.Batching

/-- Definition 1 / Definition 13 (pp. 2, 14): the diameter `max_{i,j ∈ e} |i - j|` of a hyperedge
`e ⊆ ℕ`, i.e. its largest minus its smallest vertex (`0` for the empty set, which never occurs
for an edge of a shareability hypergraph). -/
def diam (e : Finset ℕ) : ℕ :=
  if h : e.Nonempty then e.max' h - e.min' h else 0

/-- Definition 1 (p. 2): `(V, E, w)` with `V = [n] = {1, …, n}` is a shareability hypergraph with
parameters `(n, d, k)`: every hyperedge is a non-empty subset of `[n]` of diameter `< d` and of
cardinality `≤ k`, with non-negative weight. (Non-emptiness of hyperedges is the field's standing
convention; the paper does not state it.) -/
def IsShareability (n d k : ℕ) (E : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) : Prop :=
  ∀ e ∈ E, e ⊆ Finset.Icc 1 n ∧ e.Nonempty ∧ diam e < d ∧ e.card ≤ k ∧ 0 ≤ w e

/-- Definition 10 (p. 14): `M` is a matching in the hypergraph with edge set `E`: `M ⊆ E` and the
edges of `M` are pairwise disjoint. -/
def IsMatching (E M : Finset (Finset ℕ)) : Prop :=
  M ⊆ E ∧ (M : Set (Finset ℕ)).PairwiseDisjoint id

/-- Definition 8 (p. 14): the weight `w(M) = ∑_{e ∈ M} w(e)` of a set of edges. -/
def weight (w : Finset ℕ → ℝ) (M : Finset (Finset ℕ)) : ℝ :=
  ∑ e ∈ M, w e

/-- The vertex set `V(M)` matched by a set of edges `M` (Appendix B.3, p. 19). -/
def vertices (M : Finset (Finset ℕ)) : Finset ℕ :=
  M.biUnion id

/-- Algorithm 5, line 4 (p. 15): `σ` is a weight-sorted ordering oracle: for every finite edge set
`S`, `σ S` lists every edge of `S` exactly once, in non-increasing order of weight. Ties are
arbitrary, and may be broken differently in every call. -/
def IsSortedOrder (w : Finset ℕ → ℝ) (σ : Finset (Finset ℕ) → List (Finset ℕ)) : Prop :=
  ∀ S, (σ S).Nodup ∧ (σ S).toFinset = S ∧ (σ S).Pairwise (fun a b => w b ≤ w a)

/-- Algorithm 5, lines 6–7 (p. 15): add the edge `e` to `M` if `M ∪ {e}` is still a matching. -/
def greedyStep (M : Finset (Finset ℕ)) (e : Finset ℕ) : Finset (Finset ℕ) :=
  if ∀ f ∈ M, Disjoint e f then insert e M else M

/-- Algorithm 5 (`Greedy`, p. 15): scan the edges of `S` in the sorted order `σ S` and keep each
edge that is disjoint from every edge kept so far. -/
def greedy (σ : Finset (Finset ℕ) → List (Finset ℕ)) (S : Finset (Finset ℕ)) :
    Finset (Finset ℕ) :=
  (σ S).foldl greedyStep ∅

/-- Algorithm 2, line 3 (p. 7): the first `k` vertices of the ordered vertex set `B`
(the `k` smallest elements; all of `B` if `B` has at most `k` elements). -/
def firstK (B : Finset ℕ) (k : ℕ) : Finset ℕ :=
  B.filter (fun v => (B.filter (fun u => u < v)).card < k)

/-- Algorithm 2, line 4 (p. 7): the last `k` vertices of the ordered vertex set `B`
(the `k` largest elements; all of `B` if `B` has at most `k` elements). -/
def lastK (B : Finset ℕ) (k : ℕ) : Finset ℕ :=
  B.filter (fun v => (B.filter (fun u => v < u)).card < k)

/-- Definition 18, item 2 (p. 19): every edge of `M` meets both `L` and `R`. -/
def IsRestricted (L R : Finset ℕ) (M : Finset (Finset ℕ)) : Prop :=
  ∀ e ∈ M, (e ∩ L).Nonempty ∧ (e ∩ R).Nonempty

open Classical in
/-- Definition 18 (p. 19): `M_{L,R}`, the matchings in the hypergraph with edge set `EB` all of
whose edges meet both `L` and `R`. (The paper's side condition `L ∩ R = ∅` is not imposed.) -/
noncomputable def restrictedMatchings (EB : Finset (Finset ℕ)) (L R : Finset ℕ) :
    Finset (Finset (Finset ℕ)) :=
  EB.powerset.filter (fun M => IsMatching EB M ∧ IsRestricted L R M)

theorem empty_mem_restrictedMatchings (EB : Finset (Finset ℕ)) (L R : Finset ℕ) :
    ∅ ∈ restrictedMatchings EB L R := by
  classical
  unfold restrictedMatchings
  exact Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset EB,
    ⟨Finset.empty_subset EB, by rw [Finset.coe_empty]; exact Set.pairwiseDisjoint_empty⟩,
    fun e he => absurd he (Finset.notMem_empty e)⟩

/-- Algorithm 2, line 9 (p. 7): `Greedy((V \ V(M), E))`, Greedy run on the edges of `EB` that avoid
every vertex matched by `M`. -/
def greedyAvoiding (σ : Finset (Finset ℕ) → List (Finset ℕ)) (EB M : Finset (Finset ℕ)) :
    Finset (Finset ℕ) :=
  greedy σ (EB.filter (fun e => Disjoint e (vertices M)))

/-- Algorithm 2, line 10 (p. 7): a matching `M_{i*} ∈ M_{L,R}` maximizing
`w(M ∪ Greedy((V \ V(M), E)))`, with `L`, `R` the first and last `k` vertices of `B`. -/
noncomputable def depthKChoice (σ : Finset (Finset ℕ) → List (Finset ℕ)) (w : Finset ℕ → ℝ)
    (k : ℕ) (B : Finset ℕ) (EB : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  Classical.choose (Finset.exists_max_image (restrictedMatchings EB (firstK B k) (lastK B k))
    (fun M => weight w (M ∪ greedyAvoiding σ EB M))
    ⟨∅, empty_mem_restrictedMatchings EB _ _⟩)

/-- Algorithm 2 (`Depth-k Greedy`, p. 7) on the batch with ordered vertex set `B` and edge set
`EB`: returns `M_{i*} ∪ Greedy((V \ V(M_{i*}), E))`. -/
noncomputable def depthKGreedy (σ : Finset (Finset ℕ) → List (Finset ℕ)) (w : Finset ℕ → ℝ)
    (k : ℕ) (B : Finset ℕ) (EB : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  depthKChoice σ w k B EB ∪ greedyAvoiding σ EB (depthKChoice σ w k B EB)

/-- Proof of Theorem 2, p. 6 / Appendix B.3, p. 17: the batch window
`V_{z,i} = {z + i d, …, z + (i + 1) d - 1} ∩ [n]` (computed in `ℤ`, `i ∈ ℤ`). -/
def window (n d z : ℕ) (i : ℤ) : Finset ℕ :=
  (Finset.Icc 1 n).filter
    (fun v => (z : ℤ) + i * d ≤ (v : ℤ) ∧ (v : ℤ) ≤ (z : ℤ) + (i + 1) * d - 1)

/-- `E_{z,i} = {e ∈ E : e ⊆ V_{z,i}}` (p. 6). -/
def batchEdges (E : Finset (Finset ℕ)) (n d z : ℕ) (i : ℤ) : Finset (Finset ℕ) :=
  E.filter (fun e => e ⊆ window n d z i)

/-- The batch indices `i ∈ {-1, 0, …, ⌊n/d⌋}`; for `z < d` their windows cover `[n]`. -/
noncomputable def batchIndices (n d : ℕ) : Finset ℤ :=
  Finset.Icc (-1) ((n : ℤ) / (d : ℤ))

/-- `E_z = ⋃_i E_{z,i}` (p. 6). -/
noncomputable def shiftEdges (E : Finset (Finset ℕ)) (n d z : ℕ) : Finset (Finset ℕ) :=
  (batchIndices n d).biUnion (fun i => batchEdges E n d z i)

/-- Algorithm 1 (`Randomized-Batching`, p. 5) with subroutine `A = Depth-k Greedy`, for the
realized shift `Z = z`: `M_z = ⋃_i DepthKGreedy(W_{z,i})`. -/
noncomputable def randomizedBatching (σ : Finset (Finset ℕ) → List (Finset ℕ))
    (w : Finset ℕ → ℝ) (n d k : ℕ) (E : Finset (Finset ℕ)) (z : ℕ) : Finset (Finset ℕ) :=
  (batchIndices n d).biUnion
    (fun i => depthKGreedy σ w k (window n d z i) (batchEdges E n d z i))

end HyperMatchDelay.Batching
