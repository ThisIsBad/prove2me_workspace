import Mathlib

namespace SingleMachinePrec.Framework

variable {N : Type*}

/-- Two elements `x, y` are incomparable in the relation `P` (written `x ∥ y` on p. 655) when
neither `(x, y) ∈ P` nor `(y, x) ∈ P`. -/
def Incomparable (P : N → N → Prop) (x y : N) : Prop :=
  ¬ P x y ∧ ¬ P y x

/-- `inc(P)`: the set of *ordered* incomparable pairs `(x, y) ∈ N × N` with `x ∥ y` (p. 655),
as a type. These are the vertices of both graphs `G^S_P` and `G_P`. -/
def IncPair (P : N → N → Prop) : Type _ :=
  {u : N × N // Incomparable P u.1 u.2}

noncomputable instance IncPair.instFintype [Fintype N] (P : N → N → Prop) :
    Fintype (IncPair P) := by
  classical
  exact Subtype.fintype _

instance IncPair.instDecidableEq [DecidableEq N] (P : N → N → Prop) :
    DecidableEq (IncPair P) :=
  inferInstanceAs (DecidableEq {u : N × N // Incomparable P u.1 u.2})

/-- A linear extension of `P` (p. 655): a linear order `le` on `N` (reflexive, antisymmetric,
transitive, total) that contains `P`, i.e. `(x, y) ∈ P` implies `x ≤ y` in `le`. -/
structure LinearExtension (P : N → N → Prop) where
  /-- The linear order, as a relation: `le x y` means `x ≤ y`. -/
  le : N → N → Prop
  isLinearOrder : IsLinearOrder N le
  extends_P : ∀ x y, P x y → le x y

/-- The linear extension `L` *reverses* the incomparable pair `u = (x, y)` when `y < x` in `L`
(p. 655), i.e. `y ≤ x` in `L` and `y ≠ x`. -/
def LinearExtension.Reverses {P : N → N → Prop} (L : LinearExtension P) (u : IncPair P) :
    Prop :=
  L.le u.1.2 u.1.1 ∧ u.1.2 ≠ u.1.1

open Classical in
/-- A `k : t`-realizer (p. 655): a nonempty multiset `{L_1, …, L_t}` of linear extensions of `P`,
indexed by `Fin t`, such that every incomparable pair `(x, y)` is reversed by at least `k` of
them: `|{i : y < x in L_i}| ≥ k`. -/
def IsKFoldRealizer (P : N → N → Prop) (k t : ℕ) (L : Fin t → LinearExtension P) : Prop :=
  0 < t ∧ ∀ u : IncPair P, k ≤ (Finset.univ.filter (fun i => (L i).Reverses u)).card

/-- The linear extension `L` reverses every incomparable pair of `U`. -/
def LinearExtension.ReversesAll {P : N → N → Prop} (L : LinearExtension P)
    (U : Set (IncPair P)) : Prop :=
  ∀ u ∈ U, L.Reverses u

/-- An edge of the hypergraph of incomparable pairs `𝓗_P` (Felsner–Trotter, §3, p. 656): a set
`U` of incomparable pairs that is minimal under inclusion among the sets of incomparable pairs
that no linear extension of `P` reverses entirely. -/
def IsIncHyperedge (P : N → N → Prop) (U : Set (IncPair P)) : Prop :=
  (¬ ∃ L : LinearExtension P, L.ReversesAll U) ∧
    ∀ U' : Set (IncPair P), U' ⊂ U → ∃ L : LinearExtension P, L.ReversesAll U'

/-- The graph of incomparable pairs `G_P` (§3, p. 656): its vertices are the incomparable pairs
of `P`, and its edges are the edges of size 2 of the hypergraph `𝓗_P`. -/
def incPairsGraph (P : N → N → Prop) : SimpleGraph (IncPair P) where
  Adj u v := u ≠ v ∧ IsIncHyperedge P {u, v}
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Set.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

end SingleMachinePrec.Framework
