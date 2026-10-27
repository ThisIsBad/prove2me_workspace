import Mathlib
import Definitions.Def_NSWApxHard_Reduction_CubicVC

namespace NSWApxHard.Reduction

open Finset

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- The edges of `G`. -/
abbrev Edge : Type := {e : Sym2 (Fin N) // e ∈ G.edgeFinset}

/-- The vertex-edge pairs `(v, e)` with `v ∈ e`. -/
abbrev Inc : Type := {p : Fin N × Sym2 (Fin N) // p.2 ∈ G.edgeFinset ∧ p.1 ∈ p.2}

/-- The agents of the reduced instance (Lee, p. 2): a vertex agent `a(v)` (`inl v`) for every
vertex and an edge agent `a(e)` (`inr e`) for every edge. -/
abbrev Agent : Type := Fin N ⊕ Edge G

/-- The items of the reduced instance (Lee, p. 2): `k` vertex items (`inl j`), an edge item
`i(e)` (`inr (inl e)`) for every edge, and a shared item `i(v, e)` (`inr (inr (v, e))`) for every
vertex-edge pair with `v ∈ e`. -/
abbrev Item (k : ℕ) : Type := Fin k ⊕ (Edge G ⊕ Inc G)

variable {G}

/-- The vertex agent `a(v)` of the shared item `i(v, e)`. -/
def Inc.vAgent (s : Inc G) : Agent G := Sum.inl s.1.1

/-- The edge agent `a(e)` of the shared item `i(v, e)`. -/
def Inc.eAgent (s : Inc G) : Agent G := Sum.inr ⟨s.1.2, s.2.1⟩

/-- The shared item `i(v, e)` as an item. -/
def Inc.item {k : ℕ} (s : Inc G) : Item G k := Sum.inr (Sum.inr s)

variable (G)

/-- The utilities of the reduced instance (Lee, p. 2): a vertex item is worth 1 to every vertex
agent and 0 to every edge agent; the edge item `i(e)` is worth `1 - α` to `a(e)` and 0 to every
other agent; the shared item `i(v, e)` is worth `1/3` to `a(v)`, `α` to `a(e)` and 0 to every
other agent. -/
noncomputable def redUtil (k : ℕ) (α : ℝ) : Agent G → Item G k → ℝ
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inl _, Sum.inr (Sum.inl _) => 0
  | Sum.inr e, Sum.inr (Sum.inl e') => if e = e' then 1 - α else 0
  | Sum.inl v, Sum.inr (Sum.inr s) => if s.1.1 = v then 1 / 3 else 0
  | Sum.inr e, Sum.inr (Sum.inr s) => if e.1 = s.1.2 then α else 0

variable {G}

/-- The number of vertex items the vertex agent `a(v)` holds under the allocation `x`. -/
def vItems {k : ℕ} (x : Item G k → Agent G) (v : Fin N) : ℕ :=
  (univ.filter (fun j : Fin k => x (Sum.inl j) = Sum.inl v)).card

/-- The number of shared items other than `s` that the agent `ag` holds under `x`. -/
def sharedOther {k : ℕ} (x : Item G k → Agent G) (ag : Agent G) (s : Inc G) : ℕ :=
  (univ.filter (fun s' : Inc G => s' ≠ s ∧ x (Sum.inr (Sum.inr s')) = ag)).card

/-- The rule of Lemma 2.3 (Lee, p. 3) for the shared item `s = i(v, e)` under the allocation `x`:
1. if `a(v)` has 1 vertex item, `a(e)` gets `i(v, e)`;
2. elseif `a(e)` has 1 shared item other than `i(v, e)`, `a(v)` gets `i(v, e)`;
3. elseif `a(v)` has 2 shared items other than `i(v, e)`, `a(e)` gets `i(v, e)`;
4. else `a(v)` gets `i(v, e)`. -/
def Rule {k : ℕ} (x : Item G k → Agent G) (s : Inc G) : Prop :=
  x s.item =
    if vItems x s.1.1 = 1 then s.eAgent
    else if sharedOther x s.eAgent s = 1 then s.vAgent
    else if sharedOther x s.vAgent s = 2 then s.eAgent
    else s.vAgent

end NSWApxHard.Reduction
