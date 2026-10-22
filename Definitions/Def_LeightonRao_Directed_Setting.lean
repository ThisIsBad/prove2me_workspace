import Mathlib

namespace LeightonRao.Directed

/-- Leighton–Rao, J. ACM 46 (1999), §1.1 p. 788 and §2.4 p. 803. A directed capacitated network on
the finite vertex set `V`: `C u v ≥ 0` is the capacity of the edge directed from `u` to `v`. An edge
`u → v` exists iff `0 < C u v`; there is no symmetry requirement, and there are no loops. -/
structure DiNetwork (V : Type) where
  /-- capacity of the directed edge `u → v` (`0` if there is no such edge) -/
  C : V → V → ℝ
  C_nonneg : ∀ u v, 0 ≤ C u v
  C_self : ∀ u, C u u = 0

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §2.4, p. 804. `C(U, Ū)`: the sum of the capacities of the edges of the cut `⟨U, Ū⟩` that are
directed from `U` to `Ū`. -/
def diCutCap (N : DiNetwork V) (U : Finset V) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v

/-- Directed analogue of the standing assumption of p. 789 ("the underlying graph is connected so
that `C(U, Ū) > 0` for all `U`"): every nonempty proper vertex set has an edge leaving it, i.e. the
digraph is strongly connected. -/
def IsStronglyConnectedNet (N : DiNetwork V) : Prop :=
  ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty → 0 < diCutCap N U

/-- §2.2 p. 795 and §2.4 p. 803. The ratio cost `C(U, Ū)/(|U||Ū|)` of the directed cut `⟨U, Ū⟩`.
Only meaningful for nonempty proper `U` (otherwise Lean returns `x / 0 = 0`). -/
noncomputable def diRatio (N : DiNetwork V) (U : Finset V) : ℝ :=
  diCutCap N U / ((U.card : ℝ) * (Uᶜ.card : ℝ))

/-- §2.4, pp. 803–804. The min-cut `𝒮 = min_{U ⊆ V} C(U, Ū)/(|U||Ū|)` of a directed UMFP, the
minimum taken over nonempty proper `U` (the ratio is `0/0` at `U = ∅, V`). The index type is
nonempty exactly when `2 ≤ Fintype.card V`; every statement using `diMinCut` assumes this. -/
noncomputable def diMinCut (N : DiNetwork V) : ℝ :=
  ⨅ U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty}, diRatio N U.1

/-- §2.4, p. 803. The demands of a directed UMFP: one unit from `u` to `v` for each ordered pair
`u ≠ v`. -/
def diDemand : V → V → ℝ := fun s t => if s = t then 0 else 1

/-- §1.1–1.2 pp. 788–789 and §2.4 p. 803. `f` is a directed concurrent flow of value `lam` for the
demands `D`: `f s t i j ≥ 0` is the amount of commodity `(s, t)` on the edge directed from `i` to
`j`; each commodity `s ≠ t` ships `lam · D s t` units from `s` to `t` (flow conservation elsewhere);
there is no commodity `(s, s)`; flow moves only in the direction of each edge, and the total flow
on the edge `i → j` is at most its capacity `C i j`. -/
def IsDiConcurrentFlow (N : DiNetwork V) (D : V → V → ℝ) (f : V → V → V → V → ℝ) (lam : ℝ) :
    Prop :=
  (∀ s t i j, 0 ≤ f s t i j) ∧
  (∀ s t, s ≠ t → ∀ v, ∑ j, f s t v j - ∑ j, f s t j v =
      lam * D s t * ((if v = s then 1 else 0) - (if v = t then 1 else 0))) ∧
  (∀ s, ∀ i j, f s s i j = 0) ∧
  (∀ i j, ∑ s, ∑ t, f s t i j ≤ N.C i j)

/-- §1.2, p. 789. The max-flow `f`: the largest fraction `lam ≥ 0` of every demand that can be
routed simultaneously. The set contains `0`; it is bounded above (by weak duality) as soon as some
commodity with positive demand is separated by a proper cut, which holds for `diDemand` when
`2 ≤ Fintype.card V`. -/
noncomputable def diMaxFlow (N : DiNetwork V) (D : V → V → ℝ) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsDiConcurrentFlow N D f lam}

/-- A directed walk from `u` to `v`: a list of vertices starting at `u`, ending at `v`, in which
every two consecutive vertices are joined by an edge (positive capacity) directed forwards. The
one-element list `[u]` is the walk of length `0` from `u` to `u`. -/
def IsDiWalk (N : DiNetwork V) (l : List V) (u v : V) : Prop :=
  l.head? = some u ∧ l.getLast? = some v ∧ l.IsChain (fun a b => 0 < N.C a b)

/-- The length `∑ d(xₖ, xₖ₊₁)` of the walk `x₀, x₁, …, x_m` with respect to the distance function
`d` (each traversed edge counted in its own direction). -/
def diLen (d : V → V → ℝ) (l : List V) : ℝ :=
  ((l.zip l.tail).map (fun e => d e.1 e.2)).sum

/-- §2.2 p. 796 and §2.4. The shortest-path distance `d(u, v)` from `u` to `v` with respect to the
distance function `d`: the infimum of the lengths of directed walks from `u` to `v`. If `v` is not
reachable from `u` the index type is empty and Lean returns `0`; every statement using `diDist`
assumes `IsStronglyConnectedNet N`. -/
noncomputable def diDist (N : DiNetwork V) (d : V → V → ℝ) (u v : V) : ℝ :=
  ⨅ l : {l : List V // IsDiWalk N l u v}, diLen d l.1

/-- §2.2, p. 796, for directed edges. The total weight `W = ∑_e C(e) d(e)` of the distance function
`d`, each directed edge counted once. -/
def diTotalWeight (N : DiNetwork V) (d : V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, N.C u v * d u v

/-- p. 806. `d(T, u) = min_{t ∈ T} d(t, u)`, the distance from the set `T` to `u` (for nonempty `T`). -/
noncomputable def diDistFrom (N : DiNetwork V) (d : V → V → ℝ) (T : Finset V) (u : V) : ℝ :=
  ⨅ t : T, diDist N d t u

/-- p. 806. `d(u, T) = min_{t ∈ T} d(u, t)`, the distance from `u` to the set `T` (for nonempty `T`). -/
noncomputable def diDistTo (N : DiNetwork V) (d : V → V → ℝ) (u : V) (T : Finset V) : ℝ :=
  ⨅ t : T, diDist N d u t

/-- p. 807 (proof of Lemma 16), the dual of the directed UMFP: the distance constraint
`∑_{(u,v) ∈ V²} d(u, v) ≥ 1`, summed over ordered pairs (demand `1` on each ordered pair). -/
def SatisfiesDiConstraint (N : DiNetwork V) (d : V → V → ℝ) : Prop :=
  1 ≤ ∑ u, ∑ v, diDist N d u v

/-- p. 804. `𝒩^Δ_in(v, G)`: the set of nodes from which `v` can be reached by a directed path of
length at most `Δ` (with respect to `d`). It always contains `v`. -/
noncomputable def inBall (N : DiNetwork V) (d : V → V → ℝ) (v : V) (Δ : ℝ) : Finset V :=
  open Classical in
  Finset.univ.filter (fun u => ∃ l : List V, IsDiWalk N l u v ∧ diLen d l ≤ Δ)

/-- p. 804. `𝒩^Δ_out(v, G)`: the set of nodes that are reachable from `v` by a directed path of
length at most `Δ` (with respect to `d`). It always contains `v`. -/
noncomputable def outBall (N : DiNetwork V) (d : V → V → ℝ) (v : V) (Δ : ℝ) : Finset V :=
  open Classical in
  Finset.univ.filter (fun u => ∃ l : List V, IsDiWalk N l v u ∧ diLen d l ≤ Δ)

end LeightonRao.Directed
