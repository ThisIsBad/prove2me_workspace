import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_WeightedCompletion

namespace SingleMachinePrec.Biclique

variable {U V : Type*}

/-- An edge biclique of the bipartite graph `G = (U, V, E)` (Definition 9.1, p. 665): sets
`A ⊆ U`, `B ⊆ V` with every pair of `A × B` an edge, i.e. a complete `|A|`-by-`|B|` subgraph.
Its value is `|A| · |B|`. -/
def IsEdgeBiclique (E : U → V → Prop) (A : Finset U) (B : Finset V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, E u v

/-- The value `k_1 · k_2` of a maximum edge biclique of `G = (U, V, E)` (Definition 9.1, p. 665):
the maximum of `|A| · |B|` over all edge bicliques `(A, B)`, the empty ones (value `0`) included. -/
noncomputable def maxBicliqueValue [Fintype U] [Fintype V] (E : U → V → Prop) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset U × Finset V)).filter
    (fun AB => IsEdgeBiclique E AB.1 AB.2)).sup (fun AB => AB.1.card * AB.2.card)

/-- The precedence constraints of the bipartite scheduling instance `S_G` (§9, p. 665): the jobs
are `U ∪ V` (here the disjoint union `U ⊕ V`) and `P = (U × V) \ E`, i.e. `u ∈ U` must precede
`v ∈ V` exactly when `(u, v)` is not an edge; there are no other constraints. -/
def precSG (E : U → V → Prop) : U ⊕ V → U ⊕ V → Prop
  | Sum.inl u, Sum.inr v => ¬ E u v
  | _, _ => False

/-- Processing times of `S_G` (§9, p. 665): `1` for the jobs of `U`, `0` for the jobs of `V`. -/
def procSG : U ⊕ V → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- Weights of `S_G` (§9, p. 665): `0` for the jobs of `U`, `1` for the jobs of `V`. -/
def weightSG : U ⊕ V → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- The value `val(σ) = Σ_j w_j C_j` of a sequence `l` of all the jobs `U ∪ V` of `S_G`. -/
noncomputable def valSG [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (l : List (U ⊕ V)) : ℝ :=
  weightedCompletion procSG weightSG Finset.univ l

/-- `l` is an optimal schedule `σ*` of `S_G`: a sequence of all the jobs `U ∪ V` that observes
`P = (U × V) \ E` and minimizes `Σ_j w_j C_j` among all such sequences. -/
def IsOptimalSG [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (E : U → V → Prop) (l : List (U ⊕ V)) : Prop :=
  IsOptimalSchedule (precSG E) procSG weightSG Finset.univ l

/-- `σ(i)` (§9, p. 666): the number of jobs of `V` scheduled in `l` before `i` jobs of `U` have
been scheduled, i.e. the jobs `v ∈ V` preceded in `l` by fewer than `i` jobs of `U`.
"Precedes" compares positions in the list (`List.idxOf`). -/
def vBefore [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (l : List (U ⊕ V)) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : V =>
    (Finset.univ.filter (fun u : U => l.idxOf (Sum.inl u) < l.idxOf (Sum.inr v))).card < i)).card

/-- The block order `U \ A → B → A → V \ B` of §9, p. 666, as a rank: `0` on `U \ A`, `1` on
`B`, `2` on `A`, `3` on `V \ B`. -/
def blockRank [DecidableEq U] [DecidableEq V] (A : Finset U) (B : Finset V) : U ⊕ V → ℕ
  | Sum.inl u => if u ∈ A then 2 else 0
  | Sum.inr v => if v ∈ B then 1 else 3

/-- `l` schedules all the jobs of `S_G` in the order `U \ A → B → A → V \ B` (§9, p. 666): it is a
sequence of `U ∪ V` whose blocks appear in that order (the order inside a block is arbitrary). -/
def InBlockOrder [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (A : Finset U) (B : Finset V) (l : List (U ⊕ V)) : Prop :=
  MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
    l.Pairwise (fun x y => blockRank A B x ≤ blockRank A B y)

end SingleMachinePrec.Biclique
