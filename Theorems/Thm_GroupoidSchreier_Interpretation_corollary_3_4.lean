import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

namespace GroupoidSchreier.Interpretation
open CategoryTheory
universe u
theorem corollary_3_4 (G : Type u) [Groupoid.{u} G] (K : G → Type u) [∀ A, Group (K A)] :
    ∃ e : H2 G K ≃ ExtClasses G K,
      ∀ (E : Extension G K) (F : WeakAction G K), IsFiberAction E F →
        e (H2.mk F) = ExtClasses.mk E := by sorry
end GroupoidSchreier.Interpretation

