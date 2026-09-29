import Mathlib

namespace ApproxCliqueWidth.Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Oum–Seymour Definition 4.1 (p. 518). A function `fstar` on pairs of subsets is an
interpolation of `f : 2^V → ℤ` if, on the domain `3^V` of **disjoint** pairs,
(i) `f*(X, V \ X) = f(X)`; (ii) (uniform) `f*(A, B) ≤ f*(C, D)` whenever `C ∩ D = ∅`,
`A ⊆ C`, `B ⊆ D`; (iii) (submodular) `f*(A, B) + f*(C, D) ≥ f*(A ∩ C, B ∪ D) + f*(A ∪ C, B ∩ D)`
for disjoint `(A, B)`, `(C, D)`; (iv) `f*(∅, ∅) = f(∅)`. Values of `fstar` on non-disjoint pairs
are never constrained. (The paper's standing assumptions on `f` — submodular with `f(∅) ≤ f(X)` —
are hypotheses of the theorems that use this notion.) -/
def IsInterpolation (f : Finset V → ℤ) (fstar : Finset V → Finset V → ℤ) : Prop :=
  (∀ X : Finset V, fstar X Xᶜ = f X) ∧
  (∀ A B C D : Finset V, Disjoint C D → A ⊆ C → B ⊆ D → fstar A B ≤ fstar C D) ∧
  (∀ A B C D : Finset V, Disjoint A B → Disjoint C D →
      fstar (A ∩ C) (B ∪ D) + fstar (A ∪ C) (B ∩ D) ≤ fstar A B + fstar C D) ∧
  fstar ∅ ∅ = f ∅

/-- Oum–Seymour p. 519: `f_min(X, Y) = min_{X ⊆ Z ⊆ V \ Y} f(Z)`. The family
`{Z | X ⊆ Z, Z ∩ Y = ∅}` is nonempty exactly when `X ∩ Y = ∅` (i.e. on `3^V`); on the
non-disjoint pairs, outside the paper's domain, the value `0` is a placeholder never used. -/
noncomputable def fmin (f : Finset V → ℤ) (X Y : Finset V) : ℤ :=
  if h : (Finset.univ.filter (fun Z : Finset V => X ⊆ Z ∧ Disjoint Z Y)).Nonempty then
    (Finset.univ.filter (fun Z : Finset V => X ⊆ Z ∧ Disjoint Z Y)).inf' h f
  else 0

end ApproxCliqueWidth.Certificate
