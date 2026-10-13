import Mathlib

namespace StrategyProofArrow.Correspondence

/-- A weak order on `A` (the paper's `π_m`, p. 6): `rel x y` reads "x is preferred or
indifferent to y". Completeness gives reflexivity. -/
structure WeakOrder (A : Type*) where
  rel : A → A → Prop
  total : ∀ x y, rel x y ∨ rel y x
  trans : ∀ x y z, rel x y → rel y z → rel x z

/-- Two weak orders with the same relation are equal. -/
@[ext] theorem WeakOrder.ext {A : Type*} {R S : WeakOrder A} (h : R.rel = S.rel) : R = S := by
  cases R; cases S; cases h; rfl

/-- Strict part: `x R̄ y` means `x R y` and not `y R x` (p. 6). -/
def WeakOrder.strict {A : Type*} (R : WeakOrder A) (x y : A) : Prop := R.rel x y ∧ ¬ R.rel y x

/-- A strong order (the paper's `ρ_m`, p. 8): a weak order with no indifference between
distinct alternatives. -/
def WeakOrder.IsStrong {A : Type*} (R : WeakOrder A) : Prop :=
  ∀ x y, R.rel x y → R.rel y x → x = y

/-- The set `ρ_m` of strong orders on `A`. -/
abbrev StrongOrder (A : Type*) := {R : WeakOrder A // R.IsStrong}

/-- Strict ballot sets `ρ^n_m`: one strong order per individual. -/
abbrev StrongProfile (ι A : Type*) := ι → StrongOrder A

/-- The choice function `Ψ_W(R)` (p. 9): the `R`-maximal elements of `W`. -/
def Psi {A : Type*} (W : Set A) (R : WeakOrder A) : Set A := {x | x ∈ W ∧ ∀ y ∈ W, R.rel x y}

/-- `θ_W(C) = θ_W(D)` (p. 9): the two relations agree on `W × W`. -/
def AgreeOn {A : Type*} (W : Set A) (C D : WeakOrder A) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, (C.rel x y ↔ D.rel x y)

/-- A strict voting procedure `v : ρ^n_m → S_m` is strategy-proof (pp. 7–9): no individual `i`
at any strict ballot set `B` has a strict ballot `b` with `v(B with B_i replaced by b) B̄_i v(B)`. -/
def StrategyProof {ι A : Type*} [DecidableEq ι] (v : StrongProfile ι A → A) : Prop :=
  ∀ (B : StrongProfile ι A) (i : ι) (b : StrongOrder A),
    ¬ (B i).1.strict (v (Function.update B i b)) (v B)

/-- `u` underlies `v` (p. 32), equivalently `v` is derived from `u` (p. 30):
`Ψ_S[u(B)] = {v(B)}` for every strict ballot set `B`, where `S` is the whole alternative set. -/
def Underlies {ι A : Type*} (u : StrongProfile ι A → StrongOrder A)
    (v : StrongProfile ι A → A) : Prop :=
  ∀ B, Psi Set.univ (u B).1 = {v B}

/-- Citizens' sovereignty (p. 29), for distinct alternatives: for all `x ≠ y` some strict ballot
set has `x Ā y`. -/
def CS {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ x y : A, x ≠ y → ∃ B, (u B).1.strict x y

/-- Pareto optimality (p. 31): if every individual strictly prefers `x` to `y` in `B`, then
`x Ā y` where `A = u(B)`. -/
def PO {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (B : StrongProfile ι A) (x y : A), (∀ i, (B i).1.strict x y) → (u B).1.strict x y

/-- Independence of irrelevant alternatives (p. 29): for every `W ⊆ S_m` and strict ballot sets
`C, D` with `θ_W(C_i) = θ_W(D_i)` for all `i`, `Ψ_W(A_C) = Ψ_W(A_D)`. -/
def IIA {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (W : Set A) (C D : StrongProfile ι A),
    (∀ i, AgreeOn W (C i).1 (D i).1) → Psi W (u C).1 = Psi W (u D).1

/-- Non-negative response (p. 31): for every `x`, with `W = S_m - {x}`, and strict ballot sets
`C, D` such that (a) `θ_W(C_i) = θ_W(D_i)`, (b) `x C_i y ⇒ x D_i y` and (c) `x C̄_i y ⇒ x D̄_i y`
for all `i` and all `y ∈ W`: whenever `x Ā_C z` for `z ∈ W`, also `x Ā_D z`. -/
def NNR {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (x : A) (C D : StrongProfile ι A),
    (∀ i, AgreeOn ({x}ᶜ : Set A) (C i).1 (D i).1) →
    (∀ i, ∀ y, y ≠ x → (C i).1.rel x y → (D i).1.rel x y) →
    (∀ i, ∀ y, y ≠ x → (C i).1.strict x y → (D i).1.strict x y) →
    ∀ z, z ≠ x → (u C).1.strict x z → (u D).1.strict x z

/-- The relation of Gibbard's `Δ_xy(R)` (pp. 32–33): `x` and `y` are above every other
alternative and ordered between themselves as in `R`; the other alternatives are ordered by `Q`. -/
def deltaRel {A : Type*} (Q R : WeakOrder A) (x y : A) (w z : A) : Prop :=
  ((w = x ∨ w = y) ∧ (z = x ∨ z = y) ∧ R.rel w z) ∨
  ((w = x ∨ w = y) ∧ ¬ (z = x ∨ z = y)) ∨
  (¬ (w = x ∨ w = y) ∧ ¬ (z = x ∨ z = y) ∧ Q.rel w z)

/-- Gibbard's `Δ_xy` (pp. 32–33) as a map `ρ_m → ρ_m`, for a fixed strong order `Q`. -/
def delta {A : Type*} (Q : StrongOrder A) (x y : A) (R : StrongOrder A) : StrongOrder A :=
  ⟨{ rel := deltaRel Q.1 R.1 x y
     total := by
       intro w z
       unfold deltaRel
       by_cases hw : (w = x ∨ w = y) <;> by_cases hz : (z = x ∨ z = y) <;>
         simp only [hw, hz, true_and, false_and, not_true_eq_false, not_false_eq_true, and_true,
           and_false, or_false, false_or, or_true]
       · exact R.1.total w z
       · exact Q.1.total w z
     trans := by
       intro a b c hab hbc
       unfold deltaRel at *
       by_cases ha : (a = x ∨ a = y) <;> by_cases hb : (b = x ∨ b = y) <;>
         by_cases hc : (c = x ∨ c = y) <;>
         simp only [ha, hb, hc, true_and, false_and, not_true_eq_false, not_false_eq_true,
           and_true, and_false, or_false, false_or, or_true] at hab hbc ⊢
       · exact R.1.trans _ _ _ hab hbc
       · exact Q.1.trans _ _ _ hab hbc },
   by
     intro w z h1 h2
     unfold deltaRel at h1 h2
     by_cases hw : (w = x ∨ w = y) <;> by_cases hz : (z = x ∨ z = y) <;>
       simp only [hw, hz, true_and, false_and, not_true_eq_false, not_false_eq_true, and_true,
         and_false, or_false, false_or, or_true] at h1 h2
     · exact R.2 w z h1 h2
     · exact Q.2 w z h1 h2⟩

/-- Gibbard's relation `P` for the ballot set `B` (p. 33), as a weak relation: `x P y` iff
`x = y` or `x = v[Δ_xy(B_1), …, Δ_xy(B_n)]`. For `x ≠ y` its strict part is the paper's `x P̄ y`. -/
def gibbardRel {ι A : Type*} (v : StrongProfile ι A → A) (Q : StrongOrder A)
    (B : StrongProfile ι A) (x y : A) : Prop :=
  x = y ∨ x = v (fun i => delta Q x y (B i))

end StrategyProofArrow.Correspondence
