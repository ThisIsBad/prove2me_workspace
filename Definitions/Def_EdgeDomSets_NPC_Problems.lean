import Mathlib
import Definitions.Def_CookLevin_Complexity
import Definitions.Def_NPGraph_Encoding

namespace EdgeDomSets.NPC

/-! ## Edge dominating sets (p. 364) -/

/-- `F` is an edge dominating set of `G` (p. 364): `F` is a set of edges of `G`, and every edge
of `G` outside `F` shares a vertex with some edge of `F`. -/
def IsEdgeDominating {V : Type*} (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (∀ f ∈ F, f ∈ G.edgeSet) ∧ ∀ e ∈ G.edgeSet, e ∉ F → ∃ f ∈ F, ∃ v, v ∈ e ∧ v ∈ f

/-- The vertex `w` has at most `m` neighbours in `G`: every finite set of neighbours of `w`
has at most `m` elements (for a finite graph, `deg w ≤ m`). -/
def DegreeLE {V : Type*} (G : SimpleGraph V) (w : V) (m : ℕ) : Prop :=
  ∀ s : Finset V, (∀ v ∈ s, G.Adj w v) → s.card ≤ m

/-- Every vertex of `G` has degree at most `m` ("maximum degree `m`" read as `Δ(G) ≤ m`). -/
def MaxDegreeLE {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ w, DegreeLE G w m

/-! ## The edge dominating set problem on bipartite graphs of maximum degree 3 (pp. 365–366) -/

/-- The simple graph on `Fin n` described by the graph data `G` of the published graph code
`NPGraph` (vertex count `n` and row-major adjacency bits). -/
def toSimpleGraph (G : NPGraph.Graph) : SimpleGraph (Fin G.order) :=
  SimpleGraph.fromRel fun u v => NPGraph.Adj G u.val v.val

/-- The edge dominating set problem restricted to bipartite graphs with maximum degree 3, as a
language: the codes `encodeNat n ++ encodeNat k ++ (adjacency bits)` of a finite simple graph `G`
and a positive integer `k` such that `G` is bipartite, every vertex of `G` has degree at most 3,
and `G` has a set of at most `k` edges which dominate all the other edges. -/
def edsBip3Lang : CookLevin.Language := fun x =>
  ∃ (G : NPGraph.Graph) (k : ℕ),
    x = NPGraph.encodeInstance G k ∧ NPGraph.IsSimple G ∧
    (toSimpleGraph G).Colorable 2 ∧ MaxDegreeLE (toSimpleGraph G) 3 ∧ 1 ≤ k ∧
    ∃ F : Finset (Sym2 (Fin G.order)), IsEdgeDominating (toSimpleGraph G) F ∧ F.card ≤ k

/-! ## The SAT-3-restricted problem (p. 365) -/

/-- Number of occurrences of the positive literal `x_v` in the formula, over all clauses. -/
def posCount (φ : CookLevin.Formula) (v : ℕ) : ℕ :=
  (φ.map fun c => c.count (CookLevin.Literal.Pos v)).sum

/-- Number of occurrences of the negated literal `x̄_v` in the formula, over all clauses. -/
def negCount (φ : CookLevin.Formula) (v : ℕ) : ℕ :=
  (φ.map fun c => c.count (CookLevin.Literal.Neg v)).sum

/-- A SAT-3-restricted instance (p. 365): every clause has at most three literals, and every
variable that occurs in the formula occurs exactly twice as a positive literal and exactly once
negated. -/
def IsSat3Restricted (φ : CookLevin.Formula) : Prop :=
  (∀ c ∈ φ, c.length ≤ 3) ∧
    ∀ v ∈ CookLevin.variablesList φ, posCount φ v = 2 ∧ negCount φ v = 1

/-- The SAT-3-restricted problem as a language: codes of satisfiable SAT-3-restricted formulas. -/
def sat3rLang : CookLevin.Language := fun x =>
  ∃ φ : CookLevin.Formula,
    x = CookLevin.encodeFormula φ ∧ IsSat3Restricted φ ∧ CookLevin.Satisfiable φ

/-- The number `n` of distinct variables occurring in the formula. -/
def numVars (φ : CookLevin.Formula) : ℕ :=
  (CookLevin.variablesList φ).dedup.length

end EdgeDomSets.NPC
