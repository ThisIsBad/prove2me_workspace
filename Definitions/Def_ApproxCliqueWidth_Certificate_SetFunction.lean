import Mathlib

namespace ApproxCliqueWidth.Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Oum–Seymour p. 516: `f : 2^V → ℤ` is submodular if
`f(X) + f(Y) ≥ f(X ∩ Y) + f(X ∪ Y)` for all `X, Y ⊆ V`. -/
def IsSubmodular (f : Finset V → ℤ) : Prop :=
  ∀ X Y : Finset V, f (X ∩ Y) + f (X ∪ Y) ≤ f X + f Y

/-- Oum–Seymour p. 516: `f` is symmetric if `f(X) = f(V \ X)` for all `X ⊆ V`. -/
def IsSymmetric (f : Finset V → ℤ) : Prop :=
  ∀ X : Finset V, f X = f Xᶜ

/-- Oum–Seymour p. 517, matroid rank axioms (i)–(iii), for a rank function on the ground set
`E ⊆ V`: `r` restricted to subsets of `E` satisfies `0 ≤ r(X) ≤ |X|`, is monotone and is
submodular. Values of `r` on sets not contained in `E` are unconstrained. -/
def IsMatroidRankOn (E : Finset V) (r : Finset V → ℤ) : Prop :=
  (∀ X : Finset V, X ⊆ E → 0 ≤ r X ∧ r X ≤ (X.card : ℤ)) ∧
  (∀ X Y : Finset V, X ⊆ Y → Y ⊆ E → r X ≤ r Y) ∧
  (∀ X Y : Finset V, X ⊆ E → Y ⊆ E → r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y)

/-- Oum–Seymour Definition 5.1 (p. 519): `W ⊆ V` is well-linked with respect to `f` if for every
partition `(X, Y)` of `W` and every `Z` with `X ⊆ Z ⊆ V \ Y`, `f(Z) ≥ min(|X|, |Y|)`.
(The paper states the notion for symmetric submodular `f` with `f(∅) = 0`; those assumptions
are hypotheses of the theorems that use it.) -/
def IsWellLinked (f : Finset V → ℤ) (W : Finset V) : Prop :=
  ∀ X Y : Finset V, X ∪ Y = W → Disjoint X Y →
    ∀ Z : Finset V, X ⊆ Z → Disjoint Z Y → (min X.card Y.card : ℤ) ≤ f Z

end ApproxCliqueWidth.Certificate
