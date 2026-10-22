import Mathlib

namespace LeightonRao.Product

/-- An undirected capacitated network on the finite vertex type `V` (Leighton–Rao, §1.1–1.2,
pp. 788–789). `C u v ≥ 0` is the capacity of the undirected edge `{u, v}`; it is symmetric and
vanishes on the diagonal. The pair `{u, v}` is an edge iff `0 < C u v`. -/
structure Network (V : Type) where
  C : V → V → ℝ
  C_nonneg : ∀ u v, 0 ≤ C u v
  C_symm : ∀ u v, C u v = C v u
  C_self : ∀ u, C u u = 0

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The underlying simple graph: `u ~ v` iff the capacity of `{u, v}` is positive. -/
def Network.graph (N : Network V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => 0 < N.C u v)

/-- Cut capacity `C(U, Ū) = ∑_{u ∈ U} ∑_{v ∉ U} C(u, v)`; each undirected edge across the cut is
counted once. -/
def cutCap (N : Network V) (U : Finset V) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v

/-- The standing assumption of p. 789: the network is connected, i.e. `C(U, Ū) > 0` for every
nonempty proper vertex set `U`. -/
def IsConnectedNet (N : Network V) : Prop :=
  ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty → 0 < cutCap N U

/-- A concurrent multicommodity flow of value `lam` for the demand matrix `D` (p. 789), in arc
form: one commodity per ordered pair `(s, t)` with `s ≠ t`; `f s t i j ≥ 0` is the amount of
commodity `(s, t)` on the arc `i → j`; commodity `(s, t)` has net outflow `lam * D s t` at `s`,
net inflow `lam * D s t` at `t` and is conserved elsewhere; the diagonal commodities carry
nothing; and on every undirected edge `{i, j}` the total flow in both directions is at most
`C i j`. -/
def IsConcurrentFlow (N : Network V) (D : V → V → ℝ) (f : V → V → V → V → ℝ) (lam : ℝ) :
    Prop :=
  (∀ s t i j, 0 ≤ f s t i j) ∧
  (∀ s t, s ≠ t → ∀ v, ∑ j, f s t v j - ∑ j, f s t j v =
      lam * D s t * ((if v = s then 1 else 0) - (if v = t then 1 else 0))) ∧
  (∀ s, ∀ i j, f s s i j = 0) ∧
  (∀ i j, ∑ s, ∑ t, (f s t i j + f s t j i) ≤ N.C i j)

/-- The (concurrent) max-flow `f` (p. 789): the supremum of the values `lam ≥ 0` for which a
concurrent flow of value `lam` exists. The set contains `0`; it is bounded above as soon as some
commodity of positive demand is separated by a cut (weak duality), which holds for the product
demands of a PMFP with at least two nodes of positive weight. -/
noncomputable def maxFlow (N : Network V) (D : V → V → ℝ) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N D f lam}

/-- A distance function (p. 796): a nonnegative symmetric length `d u v`; only its values on
edges of the network matter. -/
def IsDistanceFunction (d : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ d u v) ∧ ∀ u v, d u v = d v u

/-- The total weight `W = ∑_{e ∈ E} C(e) d(e)` of a distance function (p. 796), each undirected
edge counted once. -/
noncomputable def totalWeight (N : Network V) (d : V → V → ℝ) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, N.C u v * d u v

/-- The length of a walk in the network graph with respect to the distance function `d`. -/
def walkLen (N : Network V) (d : V → V → ℝ) {u v : V} (p : N.graph.Walk u v) : ℝ :=
  (p.darts.map (fun a => d a.fst a.snd)).sum

/-- The shortest-path distance `d(u, v)` in `G` with respect to `d` (p. 796): the infimum of the
lengths of the walks from `u` to `v`. Meaningful when `u` and `v` are connected (the standing
connectivity assumption); it is `0` otherwise. -/
noncomputable def dist (N : Network V) (d : V → V → ℝ) (u v : V) : ℝ :=
  ⨅ p : N.graph.Walk u v, walkLen N d p

/-- The distance `d(T, u) = min_{t ∈ T} d(t, u)` from a vertex set `T` to `u` (it is `0` when
`T = ∅`). -/
noncomputable def distFrom (N : Network V) (d : V → V → ℝ) (T : Finset V) (u : V) : ℝ :=
  ⨅ t : T, dist N d t u

/-- `S` has radius at most `Δ` (Lemma 8 (1)): some centre `c ∈ S` reaches every `y ∈ S` by a walk
that stays inside `S` and has length at most `Δ`. -/
def HasRadiusLE (N : Network V) (d : V → V → ℝ) (S : Finset V) (Δ : ℝ) : Prop :=
  ∃ c ∈ S, ∀ y ∈ S, ∃ p : N.graph.Walk c y, (∀ x ∈ p.support, x ∈ S) ∧ walkLen N d p ≤ Δ

/-- The capacity of the edges linking nodes in different parts of the partition `P`, each
undirected edge counted once. -/
noncomputable def crossCap (N : Network V) (P : Finpartition (Finset.univ : Finset V)) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, if P.part u = P.part v then 0 else N.C u v

/-- The node weight of a set: `π(U) = ∑_{u ∈ U} π(u)` (p. 801). -/
def piSum (π : V → ℝ) (U : Finset V) : ℝ :=
  ∑ u ∈ U, π u

/-- The set `𝒫` of nodes with nonzero weight (p. 801); `p = |𝒫|`. -/
noncomputable def support (π : V → ℝ) : Finset V :=
  Finset.univ.filter (fun u => π u ≠ 0)

/-- A PMFP node weighting (p. 801): `π(u) ≥ 0` for every node, normalized (the paper's "without
loss of generality") so that `∑_{u ∈ V} π(u) = p = |𝒫|`. -/
def IsPMFPWeight (π : V → ℝ) : Prop :=
  (∀ u, 0 ≤ π u) ∧ ∑ u, π u = ((support π).card : ℝ)

/-- The product demands (p. 801, footnote 7): for each ordered pair `u ≠ v`, a commodity from `u`
to `v` with demand `π(u)π(v)/2`, so the pair `{u, v}` has total demand `π(u)π(v)`. -/
noncomputable def productDemand (π : V → ℝ) : V → V → ℝ :=
  fun s t => if s = t then 0 else π s * π t / 2

/-- The weighted ratio cost `C(U, Ū) / (π(U) π(Ū))` of the cut `⟨U, Ū⟩` (p. 801). -/
noncomputable def weightedRatio (N : Network V) (π : V → ℝ) (U : Finset V) : ℝ :=
  cutCap N U / (piSum π U * piSum π Uᶜ)

/-- The min-cut `𝒮 = min_U C(U, Ū)/(π(U)π(Ū))` of a PMFP (p. 801), the minimum taken over the cuts
with `π(U) > 0` and `π(Ū) > 0` (on the other cuts the page's ratio is undefined). The index type is
nonempty when at least two nodes have positive weight. -/
noncomputable def pmfpMinCut (N : Network V) (π : V → ℝ) : ℝ :=
  ⨅ U : {U : Finset V // 0 < piSum π U ∧ 0 < piSum π Uᶜ}, weightedRatio N π U.1

/-- The number `k = (p choose 2)` of commodities with nonzero demand (p. 801), counted as
unordered pairs of nodes of `𝒫`. -/
noncomputable def numCommodities (π : V → ℝ) : ℕ :=
  Nat.choose (support π).card 2

/-- The weighted distance constraint of the PMFP dual (p. 802):
`∑_{{u,v} ∈ 𝒫²} π(u)π(v) d(u, v) ≥ 1`, written as half the sum over ordered pairs (the diagonal
terms vanish since `d(u, u) = 0`, and terms off `𝒫` vanish since `π = 0` there). -/
noncomputable def SatisfiesPMFPConstraint (N : Network V) (π : V → ℝ) (d : V → V → ℝ) : Prop :=
  1 ≤ (1 / 2) * ∑ u, ∑ v, π u * π v * dist N d u v

end LeightonRao.Product
