import Mathlib

namespace GroupoidSchreier.Interpretation

open CategoryTheory

universe u

/-- Proposition 2.6 (p. 7), used as the definition of a weak action (p. 15): a weak action
`⟨F, σ⟩` of the groupoid `G` on the family of groups `K`. `F u` is a group isomorphism
`K A ≃* K B` for `u : A ⟶ B`; `σ u v : K C` is the paper's `σ_{vu}` for `A ⟶[u] B ⟶[v] C`,
and `u ≫ v` is the paper's composite `vu`. -/
structure WeakAction (G : Type u) [Groupoid.{u} G] (K : G → Type u) [∀ A, Group (K A)] where
  /-- `F u = ^u(-) : K_A → K_B`, a group isomorphism -/
  F : ∀ {A B : G}, (A ⟶ B) → (K A ≃* K B)
  /-- `σ u v = σ_{vu} ∈ K_C` -/
  σ : ∀ {A B C : G}, (A ⟶ B) → (B ⟶ C) → K C
  /-- condition 1: `^1 x = x` -/
  map_id : ∀ (A : G) (x : K A), F (𝟙 A) x = x
  /-- condition 2: `σ_{11} = 1` -/
  σ_id : ∀ A : G, σ (𝟙 A) (𝟙 A) = 1
  /-- condition 3: `σ_{vu} · ^{vu}x = ^v(^u x) · σ_{vu}` -/
  conj : ∀ {A B C : G} (u : A ⟶ B) (v : B ⟶ C) (x : K A),
    σ u v * F (u ≫ v) x = F v (F u x) * σ u v
  /-- condition 4: `σ_{wv} σ_{(wv)u} = ^wσ_{vu} · σ_{w(vu)}` -/
  cocycle : ∀ {A B C D : G} (u : A ⟶ B) (v : B ⟶ C) (w : C ⟶ D),
    σ v w * σ u (v ≫ w) = F w (σ u v) * σ (u ≫ v) w

/-- Example 2.11 (pp. 9–10): a morphism `F₁ → F₂` in `Act~(G, K)`, a family of maps
`τ_{AB} : G(A, B) → K_B` satisfying naturality, normalization and coherence. -/
structure ActHom {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F₁ F₂ : WeakAction G K) where
  /-- `τ u = τ_{AB}(u) ∈ K_B` -/
  τ : ∀ {A B : G}, (A ⟶ B) → K B
  /-- naturality: `τ_{AB}(u) · F₁(u)(k) = F₂(u)(k) · τ_{AB}(u)` -/
  naturality : ∀ {A B : G} (u : A ⟶ B) (k : K A), τ u * F₁.F u k = F₂.F u k * τ u
  /-- normalization: `τ_{AA}(1) = 1` -/
  normalization : ∀ A : G, τ (𝟙 A) = 1
  /-- coherence: `F₂(v)(τ_{AB}(u)) · τ_{BC}(v) · σ¹_{vu} = σ²_{vu} · τ_{AC}(vu)` -/
  coherence : ∀ {A B C : G} (u : A ⟶ B) (v : B ⟶ C),
    F₂.F v (τ u) * τ v * F₁.σ u v = F₂.σ u v * τ (u ≫ v)

/-- Definition 3.3 (p. 15): `H²_{|AUT(K)|}(G, K) = Act~[G, K]`, the set of connected components of
the category of weak actions of `G` on `K`. `Quot` of the relation "there is a morphism" is its
equivalence closure, i.e. exactly the connected components. -/
def H2 (G : Type u) [Groupoid.{u} G] (K : G → Type u) [∀ A, Group (K A)] : Type u :=
  Quot (fun F₁ F₂ : WeakAction G K => Nonempty (ActHom F₁ F₂))

/-- The class `[F] ∈ H²_{|AUT(K)|}(G, K)` of a weak action `F` (its connected component). -/
def H2.mk {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F : WeakAction G K) : H2 G K :=
  Quot.mk _ F

end GroupoidSchreier.Interpretation
