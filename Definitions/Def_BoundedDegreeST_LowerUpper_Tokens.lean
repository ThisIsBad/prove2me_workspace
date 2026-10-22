import Definitions.Def_BoundedDegreeST_LowerUpper_LP

namespace BoundedDegreeST.LowerUpper

/-- A vertex is active if some edge of the support `E*` is incident to it. -/
def Active {V : Type*} (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (v : V) : Prop :=
  0 < degree (support E x) v

/-- Excess tokens of a vertex: its `deg_{E*}(v)` tokens minus the two tokens a
vertex of `T` needs. -/
noncomputable def vertexExcess {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (T : Finset V) (v : V) : ℤ :=
  (degree (support E x) v : ℤ) - (if v ∈ T then 2 else 0)

/-- Excess tokens of a supernode `C` (p. 668): the sum of the excess tokens of
the active vertices in `C`. -/
noncomputable def supernodeExcess {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (T : Finset V) (C : Finset V) : ℤ := by
  classical
  exact ∑ v ∈ C.filter (fun v => Active E x v), vertexExcess E x T v

/-- A special supernode (p. 668): a supernode whose excess is exactly one. -/
def IsSpecialSupernode {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (T : Finset V) (C : Finset V) : Prop :=
  C ∈ supernodes F ∧ supernodeExcess E x T C = 1

/-- `R` is a child of `S` in the forest of the laminar family `𝓛` (p. 667):
`S` is the smallest member of `𝓛` strictly containing `R`. -/
def IsChild {V : Type*} [DecidableEq V] (L : Finset (Finset V)) (S R : Finset V) : Prop :=
  R ∈ L ∧ R ⊂ S ∧ ∀ R' ∈ L, R ⊂ R' → ¬ R' ⊂ S

/-- The children of `S` in the forest of `𝓛`. -/
noncomputable def children {V : Type*} [DecidableEq V]
    (L : Finset (Finset V)) (S : Finset V) : Finset (Finset V) := by
  classical
  exact L.filter (fun R => IsChild L S R)

/-- The members of `S` (p. 669): its children in the forest of `𝓛`, together with
the supernodes `C ⊆ S` that are contained in no child of `S`. -/
noncomputable def members {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (L : Finset (Finset V)) (S : Finset V) :
    Finset (Finset V) := by
  classical
  exact children L S ∪
    (supernodes F).filter (fun C => C ⊆ S ∧ ∀ R ∈ children L S, ¬ C ⊆ R)

/-- `D(S)` (p. 669): the edges of the support `E*` whose two endpoints lie in
two different members of `S`. -/
noncomputable def crossing {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact (support E x).filter (fun e =>
    ∃ R₁ ∈ members F L S, ∃ R₂ ∈ members F L S, R₁ ≠ R₂ ∧
      ∃ u ∈ R₁, ∃ w ∈ R₂, e = s(u, w))

/-- Definition 5.5 (p. 668): a set `S ≠ V` is special if
1. `|δ(S)| = 3` (in the support `E*`);
2. `x*(δ(S)) = 1` or `x*(δ(S)) = 2`;
3. `χ_{δ(S)}` is a linear combination, in `ℝ^{E*}`, of the vectors `χ_{E(R)}`
   for the members `R ∈ 𝓛` with `R ⊆ S` (its descendants, possibly `S` itself)
   and the vectors `χ_{δ(v)}` for `v ∈ S ∩ T`. -/
def IsSpecialSet {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (S : Finset V) : Prop :=
  S ≠ Finset.univ ∧
  (cut (support E x) S).card = 3 ∧
  (BoundedDegreeST.PlusOne.edgeSum x (cut E S) = 1 ∨ BoundedDegreeST.PlusOne.edgeSum x (cut E S) = 2) ∧
  indicatorOnSupport E x (cut E S) ∈ Submodule.span ℝ
    ((fun R => indicatorOnSupport E x (internal E R)) '' {R | R ∈ L ∧ R ⊆ S} ∪
     (fun v => indicatorOnSupport E x (cut E {v})) '' {v | v ∈ S ∧ v ∈ T})

/-- A special member `R` of a set (p. 669): `R` is a special supernode or a
special set. -/
def IsSpecialMember {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (R : Finset V) : Prop :=
  IsSpecialSupernode E F x T R ∨ IsSpecialSet E x L T R

/-- The tokens of the vertices of `S` left after giving two to every vertex of
`T ∩ S` and two to every member of `𝓛` strictly inside `S`. Lemma 5.6's token
distribution exists exactly when this is at least the root's share. -/
noncomputable def surplus {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) (S : Finset V) : ℤ :=
  (∑ v ∈ S, (degree (support E x) v : ℤ)) - 2 * ((T ∩ S).card : ℤ) -
    2 * ((L.filter (fun R => R ⊂ S)).card : ℤ)

end BoundedDegreeST.LowerUpper
