import Mathlib

namespace ChvatalPolytopes.Substitution

/-- **Substitution** (Chvátal 1975, pp. 144–145). Let `G₁`, `G₂` be graphs without common
vertices and let `v` be a vertex of `G₁`. The graph obtained from `G₁` by *substituting `G₂`
for `v`* is the (disjoint) union of `G₁ − v` and `G₂` together with additional edges that join
each vertex of `G₂` to each neighbor of `v`.

Its vertex set is the disjoint sum `(V₁ − {v}) ⊕ V₂`, written `{u : V₁ // u ≠ v} ⊕ V₂`; the
disjointness `V₁ ∩ V₂ = ∅` of the paper is built into the sum type. Adjacency:
* `inl a ~ inl b` iff `a ~ b` in `G₁` (this is `G₁ − v`);
* `inr a ~ inr b` iff `a ~ b` in `G₂`;
* `inl a ~ inr w` (and `inr w ~ inl a`) iff `a` is a neighbor of `v` in `G₁`. -/
def substitute {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁) (G₂ : SimpleGraph V₂) :
    SimpleGraph ({u : V₁ // u ≠ v} ⊕ V₂) where
  Adj
    | .inl a, .inl b => G₁.Adj a b
    | .inr a, .inr b => G₂.Adj a b
    | .inl a, .inr _ => G₁.Adj a v
    | .inr _, .inl b => G₁.Adj b v
  symm := by
    constructor
    rintro (a | a) (b | b) h
    · exact G₁.adj_symm h
    · exact h
    · exact h
    · exact G₂.adj_symm h
  loopless := by
    constructor
    rintro (a | a) h
    · exact G₁.loopless.irrefl a h
    · exact G₂.loopless.irrefl a h

@[simp] theorem substitute_adj_inl_inl {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁)
    (G₂ : SimpleGraph V₂) (a b : {u : V₁ // u ≠ v}) :
    (substitute G₁ v G₂).Adj (.inl a) (.inl b) ↔ G₁.Adj a b := Iff.rfl

@[simp] theorem substitute_adj_inr_inr {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁)
    (G₂ : SimpleGraph V₂) (a b : V₂) :
    (substitute G₁ v G₂).Adj (.inr a) (.inr b) ↔ G₂.Adj a b := Iff.rfl

@[simp] theorem substitute_adj_inl_inr {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁)
    (G₂ : SimpleGraph V₂) (a : {u : V₁ // u ≠ v}) (w : V₂) :
    (substitute G₁ v G₂).Adj (.inl a) (.inr w) ↔ G₁.Adj a v := Iff.rfl

@[simp] theorem substitute_adj_inr_inl {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (v : V₁)
    (G₂ : SimpleGraph V₂) (w : V₂) (b : {u : V₁ // u ≠ v}) :
    (substitute G₁ v G₂).Adj (.inr w) (.inl b) ↔ G₁.Adj b v := Iff.rfl

end ChvatalPolytopes.Substitution
