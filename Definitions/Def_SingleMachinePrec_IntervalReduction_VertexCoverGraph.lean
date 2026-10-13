import Mathlib

namespace SingleMachinePrec.IntervalReduction

variable {J : Type*}

/-- Two jobs `x, y` are incomparable in the precedence relation `P` (written `x ∥ y` on p. 655)
when neither `(x, y) ∈ P` nor `(y, x) ∈ P`. For a reflexive `P` this forces `x ≠ y`. -/
def Incomparable (P : J → J → Prop) (x y : J) : Prop :=
  ¬ P x y ∧ ¬ P y x

/-- `inc(P)` (p. 655): the *ordered* incomparable pairs `(x, y)` of `P`, as a type. They are the
nodes of the vertex cover graph `G^S_P`. -/
def IncPair (P : J → J → Prop) : Type _ :=
  {u : J × J // Incomparable P u.1 u.2}

noncomputable instance IncPair.instFintype [Fintype J] (P : J → J → Prop) :
    Fintype (IncPair P) := by
  classical
  exact Subtype.fintype _

instance IncPair.instDecidableEq [DecidableEq J] (P : J → J → Prop) :
    DecidableEq (IncPair P) :=
  inferInstanceAs (DecidableEq {u : J × J // Incomparable P u.1 u.2})

/-- The adjacency rule of `G^S_P` as printed on p. 656: nodes `(i, j)` and `(k, ℓ)` are adjacent
if `j = k` and `i = ℓ`, or `j = k` and `(i, ℓ) ∈ P`, or `(i, ℓ) ∈ P` and `(k, j) ∈ P`. -/
def csRule (P : J → J → Prop) (u v : IncPair P) : Prop :=
  (u.1.2 = v.1.1 ∧ u.1.1 = v.1.2) ∨ (u.1.2 = v.1.1 ∧ P u.1.1 v.1.2) ∨
    (P u.1.1 v.1.2 ∧ P v.1.1 u.1.2)

/-- The vertex cover graph `G^S_P` of Correa and Schulz (§2.2, p. 656): one node for each
incomparable pair, two distinct nodes adjacent when `csRule` holds in one of the two orders
(the printed rule is not symmetric, so its symmetric closure is taken). It depends only on the
precedence relation `P`. -/
def vertexCoverGraph (P : J → J → Prop) : SimpleGraph (IncPair P) where
  Adj u v := u ≠ v ∧ (csRule P u v ∨ csRule P v u)
  symm := ⟨fun _u _v h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _u h => h.1 rfl⟩

/-- The weight `p_i · w_j` of the node `(i, j)` of `G^S_P` (p. 656), for processing times `p` and
job weights `w`. -/
def vertexWeight (P : J → J → Prop) (p w : J → ℝ) (u : IncPair P) : ℝ :=
  p u.1.1 * w u.1.2

open Classical in
/-- The minimum weight `w(C_I)` of a vertex cover of `G^S_P` with node weights `p_i · w_j`: the
minimum of `∑_{u ∈ C} p_{u.1} w_{u.2}` over the finitely many vertex covers `C` (a family that
contains the set of all nodes, so the minimum exists). -/
noncomputable def minWeightVC [Fintype J] (P : J → J → Prop) (p w : J → ℝ) : ℝ :=
  (Finset.univ.filter
      (fun C : Finset (IncPair P) => (vertexCoverGraph P).IsVertexCover (C : Set _))).inf'
    ⟨Finset.univ, by simp [SimpleGraph.isVertexCover_univ]⟩
    (fun C => ∑ u ∈ C, vertexWeight P p w u)

end SingleMachinePrec.IntervalReduction
