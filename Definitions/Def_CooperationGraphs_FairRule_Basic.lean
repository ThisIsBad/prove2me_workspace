import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Game
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- A candidate allocation rule `Y : GR → ℝ^N` (§3). A graph on `N` (a set of links, i.e. unordered
pairs of distinct players) is a `SimpleGraph (Fin n)`; `Y g i` is player `i`'s payoff `Y_i(g)`. -/
abbrev Rule (n : ℕ) := SimpleGraph (Fin n) → Fin n → ℝ

/-- `g \ a,b`: the graph `g` with the link `a,b` removed (§2, (4)). -/
def removeLink {n : ℕ} (g : SimpleGraph (Fin n)) (a b : Fin n) : SimpleGraph (Fin n) :=
  g.deleteEdges {s(a, b)}

/-- `a` and `b` are connected in `S` by `g` (§2): `a = b ∈ S`, or there is a path from `a` to `b`
along links of `g` all of whose vertices lie in `S`. (Read with both endpoints in `S`, as needed
for `S/g` to be a partition of `S`.) -/
def ConnectedIn {n : ℕ} (g : SimpleGraph (Fin n)) (S : Finset (Fin n)) (a b : Fin n) : Prop :=
  a ∈ S ∧ b ∈ S ∧ Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ g.Adj x y) a b

/-- `S/g` (§2, (5)): the partition of `S` into the classes of players connected in `S` by `g`.
`N/g`, the set of connected components of `g`, is `quot Finset.univ g`. -/
noncomputable def quot {n : ℕ} (S : Finset (Fin n)) (g : SimpleGraph (Fin n)) :
    Finset (Finset (Fin n)) :=
  S.image (fun j => S.filter (fun i => ConnectedIn g S i j))

/-- The graph-restricted game `v/g` (§4, (11)): `(v/g)_S = ∑_{T ∈ S/g} v_T`. -/
noncomputable def restrict {n : ℕ} (v : Game n) (g : SimpleGraph (Fin n)) : Game n :=
  fun S => ∑ T ∈ quot S g, v T

/-- The Shapley value operator `φ : ℝ^CL → ℝ^N` (Theorem 2, (19)): the platform's
`Supermodularity.Cooperative.ShapleyValue`, applied to `v` with its junk `∅` coordinate set to `0`. -/
noncomputable def shapley {n : ℕ} (v : Game n) : Fin n → ℝ :=
  Supermodularity.Cooperative.ShapleyValue (Function.update v ∅ 0)

/-- Condition (7): `Y` is an allocation rule for `v` — on every connected component `S ∈ N/g`
of every graph `g`, the payoffs sum to `v_S`. -/
def IsAllocationRule {n : ℕ} (v : Game n) (Y : Rule n) : Prop :=
  ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, ∑ i ∈ S, Y g i = v S

/-- The equity condition (10): for every graph `g` and every link `a,b ∈ g`,
`Y_a(g) − Y_a(g \ a,b) = Y_b(g) − Y_b(g \ a,b)`. -/
def IsEquitable {n : ℕ} (Y : Rule n) : Prop :=
  ∀ (g : SimpleGraph (Fin n)) (a b : Fin n), g.Adj a b →
    Y g a - Y (removeLink g a b) a = Y g b - Y (removeLink g a b) b

/-- A fair allocation rule for `v` (§4): conditions (7) and (10). -/
def IsFair {n : ℕ} (v : Game n) (Y : Rule n) : Prop :=
  IsAllocationRule v Y ∧ IsEquitable Y

/-- Total stability (9): for every graph `g` and link `a,b ∈ g`, `Y_a(g) ≥ Y_a(g \ a,b)`. -/
def IsTotallyStable {n : ℕ} (Y : Rule n) : Prop :=
  ∀ (g : SimpleGraph (Fin n)) (a b : Fin n), g.Adj a b → Y (removeLink g a b) a ≤ Y g a

/-- Superadditivity (12), over nonempty disjoint coalitions `S, T ∈ CL`. -/
def IsSuperadditive {n : ℕ} (v : Game n) : Prop :=
  ∀ S T : Finset (Fin n), S.Nonempty → T.Nonempty → Disjoint S T → v S + v T ≤ v (S ∪ T)

/-- `|g|`, the number of links of `g` (§7, p. 11). -/
noncomputable def numLinks {n : ℕ} (g : SimpleGraph (Fin n)) : ℕ := g.edgeSet.ncard

/-- `t_i(g) = ∑_{h ⊂ g} (−1)^{|g|+|h|+1} Y_i(h)` (proof of Theorem 4, (18a)); `h ⊂ g` is strict. -/
noncomputable def altSum {n : ℕ} (Y : Rule n) (g : SimpleGraph (Fin n)) (i : Fin n) : ℝ :=
  ∑ h ∈ univ.filter (fun h : SimpleGraph (Fin n) => h < g),
    (-1 : ℝ) ^ (numLinks g + numLinks h + 1) * Y h i

/-- The game `u^S` of the proof of Theorem 2 (p. 12): `u^S_T = ∑_{R ∈ (T ∩ S)/g} v_R`. -/
noncomputable def uGame {n : ℕ} (v : Game n) (g : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Game n :=
  fun T => ∑ R ∈ quot (T ∩ S) g, v R

/-- `W ⊆ ℝ^S` is comprehensive (§6, p. 10): `a ∈ W` and `b ≤ a` coordinatewise imply `b ∈ W`. -/
def IsComprehensive {n : ℕ} {S : Finset (Fin n)} (W : Set (↥S → ℝ)) : Prop :=
  ∀ a ∈ W, ∀ b : ↥S → ℝ, (∀ i, b i ≤ a i) → b ∈ W

/-- `W` is a proper subset of `ℝ^S` (§6, p. 10): `∅ ≠ W ≠ ℝ^S`. -/
def IsProperSubset {n : ℕ} {S : Finset (Fin n)} (W : Set (↥S → ℝ)) : Prop :=
  W.Nonempty ∧ W ≠ Set.univ

/-- A game in graph function form (§6, p. 10): for every embedded subgraph `(S, g)`
(`S ∈ N/g`), `w g S ⊆ ℝ^S` is closed, comprehensive and a proper subset of `ℝ^S`.
Values of `w g S` for `S ∉ N/g` are unconstrained and never read. -/
structure GraphFunctionGame (n : ℕ) where
  w : SimpleGraph (Fin n) → (S : Finset (Fin n)) → Set (↥S → ℝ)
  isClosed : ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, IsClosed (w g S)
  comprehensive : ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, IsComprehensive (w g S)
  proper : ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, IsProperSubset (w g S)

/-- The efficiency condition (14): for every graph `g` and component `S ∈ N/g`,
`(Y_i(g))_{i ∈ S}` lies on the boundary `∂w(S,g)` of `w(S,g)` in `ℝ^S`. -/
def IsEfficientGF {n : ℕ} (G : GraphFunctionGame n) (Y : Rule n) : Prop :=
  ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, (fun i : ↥S => Y g i) ∈ frontier (G.w g S)

end CooperationGraphs.FairRule
