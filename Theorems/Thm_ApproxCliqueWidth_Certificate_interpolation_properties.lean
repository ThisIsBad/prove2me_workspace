import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Proposition 4.1 (p. 518). -/
theorem interpolation_properties {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsub : IsSubmodular f) (hmin : ∀ X : Finset V, f ∅ ≤ f X)
    (fstar : Finset V → Finset V → ℤ) (hint : IsInterpolation f fstar) :
    (∀ X Y : Finset V, Disjoint X Y →
        ∀ Z : Finset V, X ⊆ Z → Disjoint Z Y → fstar X Y ≤ f Z) ∧
    (∀ Y : Finset V, fstar ∅ Y = f ∅) ∧
    ((∀ v : V, f {v} - f ∅ ≤ 1) →
        ∀ B : Finset V, IsMatroidRankOn Bᶜ (fun X => fstar X B - f ∅)) := by sorry

end ApproxCliqueWidth.Certificate
