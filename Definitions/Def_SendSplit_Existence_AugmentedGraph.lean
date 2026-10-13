import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

variable {n : ℕ}

/-- There is a chain (directed walk, possibly of length zero) from `i` to `j` in `G`. -/
def Reach (G : ArcGraph n) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => (a, b) ∈ G.A) i j

/-- `i` and `j` lie in the same strong component of `G`. -/
def SameComponent (G : ArcGraph n) (i j : Fin n) : Prop :=
  Reach G i j ∧ Reach G j i

/-- The strong component of `i` is a sink component: there is no chain from it to a
different strong component. -/
def InSinkComponent (G : ArcGraph n) (i : Fin n) : Prop :=
  ∀ j, Reach G i j → Reach G j i

/-- `S` contains exactly one node of each sink strong component of `G` and no other node:
the nodes `i` for which the augmented graph gets the arc `(i, ν)`. -/
def IsSinkSelection (G : ArcGraph n) (S : Finset (Fin n)) : Prop :=
  (∀ s ∈ S, InSinkComponent G s) ∧
    ∀ i, InSinkComponent G i → ∃! s, s ∈ S ∧ SameComponent G i s

/-- `ċ(∞) = lim_{t → ∞} ċ(t)`, where `ċ(t)` is the right-hand derivative of `f` at `t`.
For `f` concave on `[0, ∞)` the right derivative exists on `(0, ∞)` and is nonincreasing,
so its limit at infinity is the infimum over `t > 0`; the value lies in `[-∞, ∞)`. -/
noncomputable def slopeAtInfty (f : ℝ → ℝ) : EReal :=
  ⨅ (t : ℝ) (_ : 0 < t), ((derivWithin f (Set.Ioi t) t : ℝ) : EReal)

/-- The arcs of the augmented graph `G̲` on the nodes `Option (Fin n)`, where `none` is the
appended node `ν`: the arcs `(i, j)` of `G`, and the arcs `(i, ν)` for `i ∈ S`. -/
def AugArc (G : ArcGraph n) (S : Finset (Fin n)) : Option (Fin n) → Option (Fin n) → Prop
  | some i, some j => (i, j) ∈ G.A
  | some i, none => i ∈ S
  | none, _ => False

/-- `l` is a chain (directed walk) in `G̲` from `u` to `w`, listed by its nodes. -/
def IsAugChain (G : ArcGraph n) (S : Finset (Fin n)) (u w : Option (Fin n))
    (l : List (Option (Fin n))) : Prop :=
  l.IsChain (AugArc G S) ∧ l.head? = some u ∧ l.getLast? = some w

/-- The cost of a chain `l` under the arc costs `cost`: the sum of the costs of its arcs. -/
noncomputable def chainCost (cost : Option (Fin n) → Option (Fin n) → EReal) (l : List (Option (Fin n))) :
    EReal :=
  (List.zipWith cost l l.tail).sum

/-- The arc costs `c̲` of `G̲`: `c̲_ij = ċ_ij(∞)` for an arc `(i, j)` inside a strong component
of `G`; the real number `b i j` for an arc `(i, j)` of `G` joining distinct strong components;
the real number `bν i` for an appended arc `(i, ν)`. -/
noncomputable def augCost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ) : Option (Fin n) → Option (Fin n) → EReal
  | some i, some j =>
      haveI := Classical.dec (SameComponent G i j)
      if SameComponent G i j then slopeAtInfty (c i j) else ((b i j : ℝ) : EReal)
  | some i, none => ((bν i : ℝ) : EReal)
  | none, _ => 0

/-- `π̲_i`: the infimum of the costs of the chains in `G̲` from node `i` to `ν`
(`⊤` if there is none). -/
noncomputable def minChainCost (G : ArcGraph n) (S : Finset (Fin n))
    (cost : Option (Fin n) → Option (Fin n) → EReal) (i : Fin n) : EReal :=
  ⨅ (l : List (Option (Fin n))) (_ : IsAugChain G S (some i) none l), chainCost cost l

/-- There is a minimum-cost chain from `u` to `ν` in `G̲`: a chain of real cost that is at
most the cost of every chain from `u` to `ν`. -/
def HasMinCostChain (G : ArcGraph n) (S : Finset (Fin n))
    (cost : Option (Fin n) → Option (Fin n) → EReal) (u : Option (Fin n)) : Prop :=
  ∃ l, IsAugChain G S u none l ∧ chainCost cost l ≠ ⊥ ∧ chainCost cost l ≠ ⊤ ∧
    ∀ l', IsAugChain G S u none l' → chainCost cost l ≤ chainCost cost l'

end SendSplit.Existence
