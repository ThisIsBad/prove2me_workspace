import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction

namespace GroupoidSchreier.Interpretation

open CategoryTheory

universe u

/-- Definitions 2.12 and 3.1 (pp. 10, 14–15): an extension of the groupoid `G` by the family of
groups `K`: a groupoid `E` with a fibration `P : E → G` bijective on objects whose fiber at every
object `A` is the group `K A`. The objects of `E` are taken to be the objects of `G` (footnote 2,
p. 11); arrows compose in functional order, `comp g f = g ∘ f`. -/
structure Extension (G : Type u) [Groupoid.{u} G] (K : G → Type u) [∀ A, Group (K A)] where
  /-- the arrows `E(A, B)` -/
  Hom : G → G → Type u
  /-- the identity arrow `1_A` of `E` -/
  id : ∀ A : G, Hom A A
  /-- composition `g ∘ f` of `E` -/
  comp : ∀ {A B C : G}, Hom B C → Hom A B → Hom A C
  /-- inverses of `E` -/
  inv : ∀ {A B : G}, Hom A B → Hom B A
  id_comp : ∀ {A B : G} (f : Hom A B), comp (id B) f = f
  comp_id : ∀ {A B : G} (f : Hom A B), comp f (id A) = f
  assoc : ∀ {A B C D : G} (h : Hom C D) (g : Hom B C) (f : Hom A B),
    comp (comp h g) f = comp h (comp g f)
  inv_comp : ∀ {A B : G} (f : Hom A B), comp (inv f) f = id A
  comp_inv : ∀ {A B : G} (f : Hom A B), comp f (inv f) = id B
  /-- the projection functor `P : E → G` (identity on objects) -/
  P : ∀ {A B : G}, Hom A B → (A ⟶ B)
  P_id : ∀ A : G, P (id A) = 𝟙 A
  P_comp : ∀ {A B C : G} (g : Hom B C) (f : Hom A B), P (comp g f) = P f ≫ P g
  /-- Definition 2.12 for an identity-on-objects functor: every arrow of `G` lifts to `E`. -/
  P_surj : ∀ {A B : G} (u : A ⟶ B), ∃ e : Hom A B, P e = u
  /-- the identification of `K A` with the fiber of `P` at `A` -/
  ι : ∀ A : G, K A → Hom A A
  ι_mul : ∀ (A : G) (x y : K A), ι A (x * y) = comp (ι A x) (ι A y)
  ι_injective : ∀ A : G, Function.Injective (ι A)
  /-- the fiber of `P` at `A` (arrows `e : A → A` with `P e = 1_A`) is exactly the image of `K A` -/
  ι_range : ∀ (A : G) (e : Hom A A), P e = 𝟙 A ↔ ∃ k : K A, ι A k = e

/-- Definition 3.1 (pp. 14–15): a morphism of extensions of `G` by `K`: a functor `E₁ → E₂`
above `G` (identity on objects; `map_P`: `P₂ ∘ map = P₁`) inducing the identity on fibers. -/
structure ExtHom {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (E₁ E₂ : Extension G K) where
  map : ∀ {A B : G}, E₁.Hom A B → E₂.Hom A B
  map_id : ∀ A : G, map (E₁.id A) = E₂.id A
  map_comp : ∀ {A B C : G} (g : E₁.Hom B C) (f : E₁.Hom A B),
    map (E₁.comp g f) = E₂.comp (map g) (map f)
  map_P : ∀ {A B : G} (e : E₁.Hom A B), E₂.P (map e) = E₁.P e
  fiber : ∀ (A : G) (k : K A), map (E₁.ι A k) = E₂.ι A k

/-- `Ext[G, K]` (Corollary 3.4, p. 15): the connected components of the category `Ext(G, K)`,
i.e. the quotient by the equivalence closure of "there is a morphism of extensions". -/
def ExtClasses (G : Type u) [Groupoid.{u} G] (K : G → Type u) [∀ A, Group (K A)] : Type (u + 1) :=
  Quot (fun E₁ E₂ : Extension G K => Nonempty (ExtHom E₁ E₂))

/-- The class `[E] ∈ Ext[G, K]` of an extension `E` (its connected component). -/
def ExtClasses.mk {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (E : Extension G K) : ExtClasses G K :=
  Quot.mk _ E

/-- Example 2.15 (p. 11): a set-theoretic section `s` of the arrow function of `P`, taking
identities to identities: `P (s u) = u` and `s (1_A) = 1_A`. -/
def IsNormalizedSection {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (E : Extension G K) (s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B) : Prop :=
  (∀ ⦃A B : G⦄ (u : A ⟶ B), E.P (s u) = u) ∧ ∀ A : G, s (𝟙 A) = E.id A

/-- Example 2.15 (pp. 11–12): `F` is the fiber weak action of `E` along the section `s`:
`^u k = s(u) k s(u)⁻¹` and `σ_{vu} = s(v) s(u) s(vu)⁻¹`, read through the fiber
identification `ι`. -/
def FiberVia {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (E : Extension G K) (s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B) (F : WeakAction G K) : Prop :=
  (∀ ⦃A B : G⦄ (u : A ⟶ B) (k : K A),
      E.ι B (F.F u k) = E.comp (s u) (E.comp (E.ι A k) (E.inv (s u)))) ∧
  ∀ ⦃A B C : G⦄ (u : A ⟶ B) (v : B ⟶ C),
      E.ι C (F.σ u v) = E.comp (s v) (E.comp (s u) (E.inv (s (u ≫ v))))

/-- `F` is a fiber weak action of `E` (Example 2.15): it is the fiber of `E` along some
normalized section. -/
def IsFiberAction {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (E : Extension G K) (F : WeakAction G K) : Prop :=
  ∃ s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B, IsNormalizedSection E s ∧ FiberVia E s F

/-- Definition 2.17 (pp. 12–13), for a weak action: composition in the twisted product
`∫_G F`, whose arrows `A → B` are pairs `(f, λ)` with `f : A ⟶ B` and `λ ∈ K_B`;
`(g, μ)(f, λ) = (gf, μ · ^gλ · σ_{gf})`, in functional order. -/
def twistedComp {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
    (F : WeakAction G K) {A B C : G} (g : (B ⟶ C) × K C) (f : (A ⟶ B) × K B) :
    (A ⟶ C) × K C :=
  (f.1 ≫ g.1, g.2 * F.F g.1 f.2 * F.σ f.1 g.1)

end GroupoidSchreier.Interpretation
