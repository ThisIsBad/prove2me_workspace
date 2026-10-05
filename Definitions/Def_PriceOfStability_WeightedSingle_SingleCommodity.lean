import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model

/-!
# Single-commodity weighted games, best-response moves and the marginal path cost

Anshelevich, Dasgupta, Kleinberg, Tardos, Wexler and Roughgarden, *The Price of Stability for
Network Design with Fair Cost Allocation*, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096,
Theorem 6.3 and its proof, p. 1620 (PDF p. 19).

**Formalization Note.** The network is a finite directed multigraph given by its arcs `E` and
their tails and heads; parallel arcs are allowed (the paper uses them, p. 1620). A strategy is
the arc set of a *simple* directed `s`–`t` path (no repeated vertex). The marginal cost
`c(P) = Σ_{e∈P} c_e/W_e` is valued in `ℝ≥0∞`, so that an arc of positive cost that nobody uses
(`W_e = 0`) contributes `+∞` rather than Lean's real default `x/0 = 0`.
-/

open scoped ENNReal

namespace PriceOfStability.WeightedSingle

/-- A finite directed multigraph on vertices `V` with arcs `E`: each arc `e` runs from its tail
`src e` to its head `tgt e`. -/
structure ArcGraph (V : Type*) (E : Type*) where
  /-- the tail of an arc -/
  src : E → V
  /-- the head of an arc -/
  tgt : E → V

variable {V ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- `P` is the arc set of a simple directed `s`–`t` path in `D`: there is a nonempty list of arcs
`e₁, …, e_m`, consecutive (`tgt eⱼ = src eⱼ₊₁`), starting at `s` and ending at `t`, whose visited
vertices `src e₁, …, src e_m, t` are pairwise distinct, and whose set of arcs is `P`. (When
`s = t` there is no such path.) -/
def IsSTPath (D : ArcGraph V E) (s t : V) (P : Finset E) : Prop :=
  ∃ l : List E, l.IsChain (fun a b => D.tgt a = D.src b) ∧ (l.map D.src ++ [t]).Nodup ∧
    l.head?.map D.src = some s ∧ l.getLast?.map D.tgt = some t ∧ l.toFinset = P

open Classical in
/-- The finite set of arc sets of simple directed `s`–`t` paths. -/
noncomputable def stPaths (D : ArcGraph V E) (s t : V) : Finset (Finset E) :=
  (Finset.univ : Finset E).powerset.filter (IsSTPath D s t)

/-- The weighted single-commodity game of Theorem 6.3 (p. 1620): every player has the same source
`s` and sink `t`, so every player's strategy family is the set of simple `s`–`t` paths; players
have weights `w` and arcs have fixed costs `c`. -/
noncomputable def singleCommodityGame (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ) :
    WeightedGame ι E :=
  ⟨fun _ => stPaths D s t, w, c⟩

/-- A best-response move of player `i` from the profile `S` to `S'` (Theorem 6.3, p. 1620: "the
cheapest improving deviation"): `S` is a profile, `S'` is obtained by letting `i` switch to a
feasible strategy `T`, `T` minimises `i`'s payment over all of `i`'s feasible strategies (the
others fixed), and the switch strictly lowers `i`'s payment. -/
def IsBRMoveBy (G : WeightedGame ι E) (i : ι) (S S' : ι → Finset E) : Prop :=
  IsProfile G S ∧ ∃ T ∈ G.strategies i, S' = Function.update S i T ∧
    payment G S' i < payment G S i ∧
    ∀ U ∈ G.strategies i, payment G S' i ≤ payment G (Function.update S i U) i

/-- A best-response move of some player from `S` to `S'`. -/
def IsBRMove (G : WeightedGame ι E) (S S' : ι → Finset E) : Prop :=
  ∃ i, IsBRMoveBy G i S S'

/-- The marginal cost of a path `P` in the state `S` (proof of Theorem 6.3, p. 1620):
`c(P) = Σ_{e∈P} c_e / W_e`, computed in `ℝ≥0∞`. An arc of positive cost with `W_e = 0` (used by
nobody) contributes `+∞`. -/
noncomputable def marginalCost (G : WeightedGame ι E) (S : ι → Finset E) (P : Finset E) : ℝ≥0∞ :=
  ∑ e ∈ P, ENNReal.ofReal (G.edgeCost e) / ENNReal.ofReal (edgeWeight G S e)

/-- The paths of the family `𝒮` that share at least one arc with `A` (for (6.1): the set `𝒫` of
paths that intersect `P₁ ∪ P₂`). -/
def pathsMeeting (𝒮 : Finset (Finset E)) (A : Finset E) : Finset (Finset E) :=
  𝒮.filter (fun P => (P ∩ A).Nonempty)

/-- The tuple `P(S)` of the proof of Theorem 6.3 (p. 1620): the values `c(P)` over all paths `P`
of the family `𝒮` (with multiplicity), sorted in increasing order. -/
noncomputable def sortedCosts (G : WeightedGame ι E) (𝒮 : Finset (Finset E))
    (S : ι → Finset E) : List ℝ≥0∞ :=
  (𝒮.val.map (marginalCost G S)).sort (· ≤ ·)

end PriceOfStability.WeightedSingle
