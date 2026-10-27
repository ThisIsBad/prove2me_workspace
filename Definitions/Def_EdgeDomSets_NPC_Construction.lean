import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Problems

namespace EdgeDomSets.NPC

/-! ## The graph `G` of the proof of THEOREM 2 (p. 367, Fig. 2) -/

/-- Literal occurrences of a formula: clause index `j` and position inside clause `j`
(both 0-based). -/
abbrev Occ (φ : CookLevin.Formula) : Type :=
  Σ j : Fin φ.length, Fin (φ.get j).length

/-- The literal at an occurrence. -/
def occLit {φ : CookLevin.Formula} (o : Occ φ) : CookLevin.Literal :=
  (φ.get o.1).get o.2

/-- `true` for a positive literal `x_v`, `false` for a negated literal `x̄_v`. -/
def isPos : CookLevin.Literal → Bool
  | .Pos _ => true
  | .Neg _ => false

/-- Vertices of `G`: per occurrence `o` a literal vertex (the paper's `(a_i, j1)`, `(b_i, j2)`,
`(c_i, j3)`), its pendant copy (`(·)'`), and a variable-side vertex (`a_i`, `b_i` for the two
positive occurrences of `x_i`, `c_i` for its negated one); per clause `j` the vertices `d_j`,
`d'_j`. -/
abbrev GV (φ : CookLevin.Formula) : Type :=
  (Occ φ ⊕ Occ φ ⊕ Occ φ) ⊕ (Fin φ.length ⊕ Fin φ.length)

/-- The literal vertex of an occurrence. -/
def lit {φ : CookLevin.Formula} (o : Occ φ) : GV φ := Sum.inl (Sum.inl o)
/-- The pendant copy `(·)'` of the literal vertex of an occurrence. -/
def pend {φ : CookLevin.Formula} (o : Occ φ) : GV φ := Sum.inl (Sum.inr (Sum.inl o))
/-- The variable-side vertex of an occurrence (`a_i`, `b_i` or `c_i`). -/
def varNode {φ : CookLevin.Formula} (o : Occ φ) : GV φ := Sum.inl (Sum.inr (Sum.inr o))
/-- The clause vertex `d_j`. -/
def dNode {φ : CookLevin.Formula} (j : Fin φ.length) : GV φ := Sum.inr (Sum.inl j)
/-- The clause vertex `d'_j`. -/
def dNode' {φ : CookLevin.Formula} (j : Fin φ.length) : GV φ := Sum.inr (Sum.inr j)

/-- The clause vertex a literal vertex is attached to: `d_j` for a positive occurrence in
clause `j`, `d'_j` for a negated one. -/
def clauseNode {φ : CookLevin.Formula} (o : Occ φ) : GV φ :=
  if isPos (occLit o) then dNode o.1 else dNode' o.1

/-- The edge relation of `G` (p. 367): literal vertex – pendant; literal vertex – its variable-side
vertex; literal vertex – `d_j` (positive) or `d'_j` (negated); `d_j – d'_j`; and, for every
variable `x_i`, each of its positive variable-side vertices (`a_i`, `b_i`) – its negated one
(`c_i`). -/
def GRel (φ : CookLevin.Formula) (a b : GV φ) : Prop :=
  (∃ o : Occ φ, a = lit o ∧ b = pend o) ∨
  (∃ o : Occ φ, a = lit o ∧ b = varNode o) ∨
  (∃ o : Occ φ, a = lit o ∧ b = clauseNode o) ∨
  (∃ j : Fin φ.length, a = dNode j ∧ b = dNode' j) ∨
  (∃ (o o' : Occ φ) (v : ℕ), occLit o = .Pos v ∧ occLit o' = .Neg v ∧
    a = varNode o ∧ b = varNode o')

/-- The graph `G(V, E)` constructed from the clauses in the proof of THEOREM 2. -/
def G (φ : CookLevin.Formula) : SimpleGraph (GV φ) :=
  SimpleGraph.fromRel (GRel φ)

/-- The printed bipartition `(S, T)` of `G` (p. 367): `true` means the class `S`
`= {a_i, b_i, (a_i, j1)', (b_i, j2)', (c_i, j3)} ∪ {d_i}`, `false` the class
`T = {c_i, (a_i, j1), (b_i, j2), (c_i, j3)'} ∪ {d'_i}`. -/
def inS {φ : CookLevin.Formula} : GV φ → Bool
  | Sum.inl (Sum.inl o) => !isPos (occLit o)
  | Sum.inl (Sum.inr (Sum.inl o)) => isPos (occLit o)
  | Sum.inl (Sum.inr (Sum.inr o)) => isPos (occLit o)
  | Sum.inr (Sum.inl _) => true
  | Sum.inr (Sum.inr _) => false

/-- The edge set `F` of part (i) (p. 367) for an assignment `α`: at every occurrence, the edge
from the literal vertex to its clause vertex (`d_j` or `d'_j`) if the literal is true under `α`,
and the edge from the literal vertex to its variable-side vertex if it is false. -/
noncomputable def assignEdges (φ : CookLevin.Formula) (α : CookLevin.Assignment) :
    Finset (Sym2 (GV φ)) := by
  classical
  exact Finset.univ.image fun o : Occ φ =>
      if CookLevin.satisfiesLiteral α (occLit o) = true then s(lit o, clauseNode o)
      else s(lit o, varNode o)

/-- The truth assignment `τ` of part (ii) (p. 367) read off an edge set `F`: `x_v = 1` iff `F`
contains the edge `((c_i, j3), c_i)` at the negated occurrence of `x_v`, and `x_v = 0`
otherwise. -/
noncomputable def assignOfEdges (φ : CookLevin.Formula) (F : Finset (Sym2 (GV φ))) :
    CookLevin.Assignment := fun v => by
  classical
  exact decide (∃ o : Occ φ, occLit o = .Neg v ∧ s(lit o, varNode o) ∈ F)

/-! ## The gadget `H` of Fig. 3 (p. 368) -/

/-- The corner `x` of `H`. -/
def hx : Fin 14 := 0
/-- The corner `y` of `H`. -/
def hy : Fin 14 := 1
/-- The corner `z` of `H`. -/
def hz : Fin 14 := 2
/-- `a1, a2, a3`: the inner vertices of the side `x – y`, from `x` to `y`. -/
def ha1 : Fin 14 := 3
def ha2 : Fin 14 := 4
def ha3 : Fin 14 := 5
/-- `b1, b2, b3`: the inner vertices of the side `x – z`, from `x` to `z`. -/
def hb1 : Fin 14 := 6
def hb2 : Fin 14 := 7
def hb3 : Fin 14 := 8
/-- `c1, c2, c3`: the inner vertices of the side `y – z`, from `y` to `z`. -/
def hc1 : Fin 14 := 9
def hc2 : Fin 14 := 10
def hc3 : Fin 14 := 11
/-- The inner vertex `u` of `H`. -/
def hu : Fin 14 := 12
/-- The inner vertex `v` of `H`. -/
def hv : Fin 14 := 13

/-- The 18 edges of `H` (Fig. 3): the three sides `x–a1–a2–a3–y`, `x–b1–b2–b3–z`,
`y–c1–c2–c3–z`, and `u–a1`, `u–b3`, `u–c1`, `v–b1`, `v–a3`, `v–c3`. -/
def HEdges : List (Fin 14 × Fin 14) :=
  [(hx, ha1), (ha1, ha2), (ha2, ha3), (ha3, hy),
   (hx, hb1), (hb1, hb2), (hb2, hb3), (hb3, hz),
   (hy, hc1), (hc1, hc2), (hc2, hc3), (hc3, hz),
   (hu, ha1), (hu, hb3), (hu, hc1),
   (hv, hb1), (hv, ha3), (hv, hc3)]

/-- The gadget graph `H` of Fig. 3. -/
def H : SimpleGraph (Fin 14) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ HEdges

/-- The attachment corner for clause position `r` (0-based): `x`, `y`, `z` for `r = 0, 1, 2`. -/
def attachIdx (r : ℕ) : Fin 14 :=
  if r = 0 then hx else if r = 1 then hy else hz

/-- The three attachment corners `x, y, z` of `H`. -/
def attach (r : Fin 3) : Fin 14 := attachIdx r.val

/-- `D` is a set of edges of `H` that dominates every edge of `H`, given that the external
attachment edges at the corners `attach s`, `s ∈ S`, belong to the dominating set: each edge of
`H` outside `D` shares a vertex with an edge of `D` or contains such a corner. -/
def EdsRestricted (S : Finset (Fin 3)) (D : Finset (Sym2 (Fin 14))) : Prop :=
  (∀ f ∈ D, f ∈ H.edgeSet) ∧
    ∀ e ∈ H.edgeSet, e ∉ D → (∃ f ∈ D, ∃ w, w ∈ e ∧ w ∈ f) ∨ ∃ s ∈ S, attach s ∈ e

/-! ## The modified graph `G*` (p. 368) -/

/-- Clause `j` is replaced by a copy of `H`: it has three literals, all of one sign, i.e. one of
its clause vertices `d_j`, `d'_j` has degree 4 in `G` (corrected reading of p. 368). -/
def IsReplaced (φ : CookLevin.Formula) (j : Fin φ.length) : Prop :=
  (φ.get j).length = 3 ∧
    ((∀ l ∈ φ.get j, ∃ v, l = CookLevin.Literal.Pos v) ∨
      (∀ l ∈ φ.get j, ∃ v, l = CookLevin.Literal.Neg v))

/-- The number `q` of replaced clauses. -/
noncomputable def numReplaced (φ : CookLevin.Formula) : ℕ :=
  Nat.card {j : Fin φ.length // IsReplaced φ j}

/-- Vertices of `G*`: those of `G` and one copy of the 14 vertices of `H` per clause. -/
abbrev GstarV (φ : CookLevin.Formula) : Type :=
  GV φ ⊕ (Fin φ.length × Fin 14)

/-- `a` is a clause vertex `d_j` or `d'_j` of a replaced clause `j`. -/
def IsRemoved (φ : CookLevin.Formula) (a : GV φ) : Prop :=
  ∃ j, IsReplaced φ j ∧ (a = dNode j ∨ a = dNode' j)

/-- The edge relation of `G*`: the edges of `G` not incident to a removed clause vertex; for a
replaced clause `j`, the edge from the literal vertex at position `r` to the corner
`attachIdx r` of the `j`-th copy of `H`; and the edges of the `j`-th copy of `H`. -/
def GstarRel (φ : CookLevin.Formula) (a b : GstarV φ) : Prop :=
  (∃ x y : GV φ, a = Sum.inl x ∧ b = Sum.inl y ∧ (G φ).Adj x y ∧
    ¬ IsRemoved φ x ∧ ¬ IsRemoved φ y) ∨
  (∃ o : Occ φ, IsReplaced φ o.1 ∧ a = Sum.inl (lit o) ∧ b = Sum.inr (o.1, attachIdx o.2.val)) ∨
  (∃ (j : Fin φ.length) (p q : Fin 14), IsReplaced φ j ∧ H.Adj p q ∧
    a = Sum.inr (j, p) ∧ b = Sum.inr (j, q))

/-- The graph `G*` obtained from `G` by replacing `d_j, d'_j` of every replaced clause by a copy
of `H`. (Copies of `H` for unreplaced clauses, and the removed `d_j, d'_j`, are isolated
vertices.) -/
def Gstar (φ : CookLevin.Formula) : SimpleGraph (GstarV φ) :=
  SimpleGraph.fromRel (GstarRel φ)

end EdgeDomSets.NPC
