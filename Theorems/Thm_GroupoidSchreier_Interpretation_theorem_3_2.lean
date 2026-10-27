import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

namespace GroupoidSchreier.Interpretation
open CategoryTheory
universe u
theorem theorem_3_2 {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] :
    (∀ F : WeakAction G K, ∃ E : Extension G K, IsFiberAction E F) ∧
    (∀ E : Extension G K, ∃ F : WeakAction G K, IsFiberAction E F) ∧
    ∀ (E₁ E₂ : Extension G K)
      (s₁ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₁.Hom A B) (s₂ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₂.Hom A B)
      (F₁ F₂ : WeakAction G K),
      IsNormalizedSection E₁ s₁ → FiberVia E₁ s₁ F₁ →
      IsNormalizedSection E₂ s₂ → FiberVia E₂ s₂ F₂ →
      ∃ e : ExtHom E₁ E₂ ≃ ActHom F₁ F₂,
        ∀ (Γ : ExtHom E₁ E₂) {A B : G} (u : A ⟶ B),
          Γ.map (s₁ u) = E₂.comp (E₂.ι B ((e Γ).τ u)⁻¹) (s₂ u) := by sorry
end GroupoidSchreier.Interpretation

