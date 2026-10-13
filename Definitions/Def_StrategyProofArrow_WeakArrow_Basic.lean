import Mathlib

namespace StrategyProofArrow.WeakArrow

/-- A weak order on `A` (Satterthwaite, p. 6, the set `π_m`): a complete and transitive relation.
`R.rel x y` reads "`x` is preferred or indifferent to `y`". Completeness gives reflexivity. -/
structure WeakOrder (A : Type*) where
  /-- The weak relation: `rel x y` is "x R y". -/
  rel : A → A → Prop
  /-- Completeness (hence reflexivity). -/
  total : ∀ x y, rel x y ∨ rel y x
  /-- Transitivity. -/
  trans : ∀ x y z, rel x y → rel y z → rel x z

variable {ι A : Type*}

/-- Strict part of a weak order (p. 6): `x R̄ y` iff `x R y` and not `y R x`. -/
def WeakOrder.strict (R : WeakOrder A) (x y : A) : Prop := R.rel x y ∧ ¬ R.rel y x

/-- A **strong order** (p. 8, the set `ρ_m`): a weak order with no indifference between distinct
alternatives. -/
def WeakOrder.IsStrong (R : WeakOrder A) : Prop := ∀ x y, R.rel x y → R.rel y x → x = y

/-- The strong orders on `A` (`ρ_m`). -/
abbrev StrongOrder (A : Type*) := {R : WeakOrder A // R.IsStrong}

/-- Ballot sets of weak orders (`π^n_m`). -/
abbrev WeakProfile (ι A : Type*) := ι → WeakOrder A

/-- Ballot sets of strong orders (`ρ^n_m`): every ballot is a strong order. -/
abbrev StrongProfile (ι A : Type*) := ι → StrongOrder A

/-- A strong ballot set read as a weak ballot set (`ρ^n_m ⊂ π^n_m`). -/
def toWeak (C : StrongProfile ι A) : WeakProfile ι A := fun i => (C i).1

/-- The choice set `Ψ_W(R)` (p. 9): the elements of `W` that `R` ranks at least as high as every
element of `W`. -/
def Psi (W : Set A) (R : WeakOrder A) : Set A := {x | x ∈ W ∧ ∀ y ∈ W, R.rel x y}

/-- `θ_W(C) = θ_W(D)` (p. 9): the two weak orders agree on `W × W`. -/
def AgreeOn (W : Set A) (C D : WeakOrder A) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, (C.rel x y ↔ D.rel x y)

/-! ### Arrow's conditions for social welfare functions on weak ballot sets (pp. 28–31)

A social welfare function is a map `u : WeakProfile ι A → WeakOrder A` (domain `π^n_m`, range in
`π_m`). -/

/-- **Citizens' sovereignty (CS)** (p. 29), for distinct alternatives: for every `x ≠ y` some ballot
set makes society strictly prefer `x` to `y`. (As printed, the condition also asks this for
`x = y`, which no strict relation satisfies.) -/
def CS (u : WeakProfile ι A → WeakOrder A) : Prop :=
  ∀ x y : A, x ≠ y → ∃ B : WeakProfile ι A, (u B).strict x y

/-- **Independence of irrelevant alternatives (IIA)** (p. 29): if every ballot of `C` agrees with
the corresponding ballot of `D` on `W`, the social choice sets `Ψ_W` coincide. -/
def IIA (u : WeakProfile ι A → WeakOrder A) : Prop :=
  ∀ (W : Set A) (C D : WeakProfile ι A),
    (∀ i, AgreeOn W (C i) (D i)) → Psi W (u C) = Psi W (u D)

/-- **Non-negative response (NNR)** (p. 31): let `W = S_m - {x}`. If (a) every ballot of `D`
agrees with that of `C` on `W`, (b) `x C_i y` implies `x D_i y` and (c) `x C̄_i y` implies
`x D̄_i y`, for all `i` and `y ∈ W`, then for every `z ∈ W`, `x Ā_C z` implies `x Ā_D z`. -/
def NNR (u : WeakProfile ι A → WeakOrder A) : Prop :=
  ∀ (x : A) (C D : WeakProfile ι A),
    (∀ i, AgreeOn {y | y ≠ x} (C i) (D i)) →
    (∀ i y, y ≠ x → (C i).rel x y → (D i).rel x y) →
    (∀ i y, y ≠ x → (C i).strict x y → (D i).strict x y) →
    ∀ z, z ≠ x → (u C).strict x z → (u D).strict x z

/-- **Dictatorial** (the negation of non-dictatorship ND, p. 29): some individual `i` such that,
for every ballot set `B` and all `x, y`, `x B̄_i y` implies `x Ā y` with `A = u(B)`. Nothing is
required where `i` is indifferent. -/
def Dictatorial (u : WeakProfile ι A → WeakOrder A) : Prop :=
  ∃ i : ι, ∀ (B : WeakProfile ι A) (x y : A), (B i).strict x y → (u B).strict x y

/-! ### The same conditions for strict social welfare functions (p. 31)

A strict social welfare function is a map `μ : StrongProfile ι A → StrongOrder A` (domain `ρ^n_m`,
range in `ρ_m`). -/

/-- CS for a strict social welfare function (p. 29, on `ρ^n_m`), for distinct alternatives. -/
def StrictCS (μ : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ x y : A, x ≠ y → ∃ B : StrongProfile ι A, (μ B).1.strict x y

/-- IIA for a strict social welfare function (p. 29, on `ρ^n_m`). -/
def StrictIIA (μ : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (W : Set A) (C D : StrongProfile ι A),
    (∀ i, AgreeOn W (C i).1 (D i).1) → Psi W (μ C).1 = Psi W (μ D).1

/-- NNR for a strict social welfare function (p. 31, on `ρ^n_m`). -/
def StrictNNR (μ : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (x : A) (C D : StrongProfile ι A),
    (∀ i, AgreeOn {y | y ≠ x} (C i).1 (D i).1) →
    (∀ i y, y ≠ x → (C i).1.rel x y → (D i).1.rel x y) →
    (∀ i y, y ≠ x → (C i).1.strict x y → (D i).1.strict x y) →
    ∀ z, z ≠ x → (μ C).1.strict x z → (μ D).1.strict x z

/-- A strict social welfare function is dictatorial (negation of ND, p. 29, on `ρ^n_m`). -/
def StrictDictatorial (μ : StrongProfile ι A → StrongOrder A) : Prop :=
  ∃ i : ι, ∀ (B : StrongProfile ι A) (x y : A), (B i).1.strict x y → (μ B).1.strict x y

/-! ### Tie-breaking functions (p. 38) -/

/-- A **tie-breaking function** (p. 38): `α` maps weak ballot sets to strong ballot sets so that
every strict preference `x B̄_i y` of every ballot is kept, `x C̄_i y` with `C = α(B)`. The ballot
`α(B)_i` may depend on the whole ballot set `B`. -/
def IsTieBreaking (α : WeakProfile ι A → StrongProfile ι A) : Prop :=
  ∀ (B : WeakProfile ι A) (i : ι) (x y : A), (B i).strict x y → (α B i).1.strict x y

/-- A **regular tie-breaking function** (p. 38): a tie-breaking function for which strong orders
`Q = (Q_1, …, Q_n)` exist such that whenever `x` and `y` are tied in `B_i`, `x C̄_i y` iff
`x Q̄_i y`, where `C = γ(B)`. -/
def IsRegular (γ : WeakProfile ι A → StrongProfile ι A) : Prop :=
  IsTieBreaking γ ∧ ∃ Q : StrongProfile ι A, ∀ (B : WeakProfile ι A) (i : ι) (x y : A),
    (B i).rel x y → (B i).rel y x → ((γ B i).1.strict x y ↔ (Q i).1.strict x y)

/-- Breaking the ties of one weak order `R` by a strong order `Q` (the single-ordering tie-breaker
`γ[u(B)]` of Lemma 11 and Theorem 3', pp. 48–49): `x` is ranked at least as high as `y` iff
`x R̄ y`, or `x` and `y` are tied in `R` and `x Q y`. This is a regular component tie-breaking
function with tie-breaking order `Q`. -/
def breakTies (Q : StrongOrder A) (R : WeakOrder A) : StrongOrder A :=
  ⟨{ rel := fun x y => R.strict x y ∨ (R.rel x y ∧ R.rel y x ∧ Q.1.rel x y)
     total := by
       intro x y
       rcases R.total x y with hxy | hyx
       · by_cases hyx : R.rel y x
         · rcases Q.1.total x y with hq | hq
           · exact Or.inl (Or.inr ⟨hxy, hyx, hq⟩)
           · exact Or.inr (Or.inr ⟨hyx, hxy, hq⟩)
         · exact Or.inl (Or.inl ⟨hxy, hyx⟩)
       · by_cases hxy : R.rel x y
         · rcases Q.1.total x y with hq | hq
           · exact Or.inl (Or.inr ⟨hxy, hyx, hq⟩)
           · exact Or.inr (Or.inr ⟨hyx, hxy, hq⟩)
         · exact Or.inr (Or.inl ⟨hyx, hxy⟩)
     trans := by
       intro x y z h1 h2
       rcases h1 with ⟨hxy, hnyx⟩ | ⟨hxy, hyx, hq1⟩ <;>
         rcases h2 with ⟨hyz, hnzy⟩ | ⟨hyz, hzy, hq2⟩
       · exact Or.inl ⟨R.trans _ _ _ hxy hyz, fun hzx => hnyx (R.trans _ _ _ hyz hzx)⟩
       · exact Or.inl ⟨R.trans _ _ _ hxy hyz, fun hzx => hnyx (R.trans _ _ _ hyz hzx)⟩
       · exact Or.inl ⟨R.trans _ _ _ hxy hyz, fun hzx => hnzy (R.trans _ _ _ hzx hxy)⟩
       · exact Or.inr ⟨R.trans _ _ _ hxy hyz, R.trans _ _ _ hzy hyx,
           Q.1.trans _ _ _ hq1 hq2⟩ },
   by
     intro x y h1 h2
     rcases h1 with ⟨hxy, hnyx⟩ | ⟨hxy, hyx, hq1⟩
     · rcases h2 with ⟨_, h⟩ | ⟨h, _, _⟩
       · exact absurd hxy h
       · exact absurd h hnyx
     · rcases h2 with ⟨_, h⟩ | ⟨_, _, hq2⟩
       · exact absurd hxy h
       · exact Q.2 x y hq1 hq2⟩

end StrategyProofArrow.WeakArrow
