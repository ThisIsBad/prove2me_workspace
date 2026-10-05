import Mathlib

/-!
# The weighted cost-sharing game of Sect. 6

Anshelevich, Dasgupta, Kleinberg, Tardos, Wexler and Roughgarden, *The Price of Stability for
Network Design with Fair Cost Allocation*, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096,
Sect. 6, p. 1619 (PDF p. 18), with the model of Sect. 2, p. 1607 (PDF p. 6).

**Formalization Note.** A strategy is a finite set of edges (resources) of a finite ground set `E`,
and each player `i` has a finite family `G.strategies i` of feasible strategies. The network
games of Theorem 6.3 are the instance in which every family is the set of arc sets of simple
`s`–`t` paths (`Def_PriceOfStability_WeightedSingle_SingleCommodity`).
-/

namespace PriceOfStability.WeightedSingle

/-- Sect. 6 (p. 1619): a weighted cost-sharing game on players `ι` and edges/resources `E`:
feasible strategies `Σᵢ` (each a set of edges), player weights `wᵢ` and fixed edge costs `c_e`. -/
structure WeightedGame (ι : Type*) (E : Type*) where
  /-- the feasible strategies of player `i`, each a set of edges -/
  strategies : ι → Finset (Finset E)
  /-- `wᵢ` -/
  weight : ι → ℝ
  /-- `c_e` (fixed edge cost) -/
  edgeCost : E → ℝ

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Standing assumptions of Sect. 6 and Sect. 2: weights `wᵢ ≥ 1` (p. 1619) and nonnegative edge
costs `c_e ≥ 0` (p. 1607). -/
def WeightedGame.IsStandard (G : WeightedGame ι E) : Prop :=
  (∀ i, 1 ≤ G.weight i) ∧ ∀ e, 0 ≤ G.edgeCost e

/-- `W_e`: the total weight of the players using `e` in the profile `S` (p. 1619). -/
def edgeWeight (G : WeightedGame ι E) (S : ι → Finset E) (e : E) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => e ∈ S i), G.weight i

/-- Player `i`'s payment `Σ_{e∈Sᵢ} (wᵢ/W_e) c_e` (p. 1619). On every edge `e ∈ Sᵢ` the
denominator satisfies `W_e ≥ wᵢ`, so it is positive whenever the weights are. -/
noncomputable def payment (G : WeightedGame ι E) (S : ι → Finset E) (i : ι) : ℝ :=
  ∑ e ∈ S i, G.weight i / edgeWeight G S e * G.edgeCost e

/-- `S` is a strategy profile: every player plays a feasible strategy. -/
def IsProfile (G : WeightedGame ι E) (S : ι → Finset E) : Prop := ∀ i, S i ∈ G.strategies i

/-- Pure Nash equilibrium (cost form, as on p. 1604): `S` is a profile and no player can lower
its payment by a unilateral switch to another feasible strategy. -/
def IsNash (G : WeightedGame ι E) (S : ι → Finset E) : Prop :=
  IsProfile G S ∧ ∀ i, ∀ T ∈ G.strategies i, payment G S i ≤ payment G (Function.update S i T) i

end PriceOfStability.WeightedSingle
