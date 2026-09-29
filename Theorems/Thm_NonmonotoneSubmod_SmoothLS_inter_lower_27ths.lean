import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1143, first 27ths display (Feige–Mirrokni–Vondrák 2011). Let
`f ≥ 0` be submodular, `A, C ⊆ X`, `B = X \ A`, `R = R(A, 1/3)` and
`F = (A ∩ C) ∪ (B \ C)`. Then
`E[f(R ∩ (B ∪ C))] ≥ (8/27) f(A ∩ C) + (2/27) f(B ∪ C) + (2/27) f(B ∩ C) + (4/27) f(C)
  + (4/27) f(F) + (1/27) f(B)`. -/
theorem inter_lower_27ths {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A C : Finset X) :
    8 / 27 * f (A ∩ C) + 2 / 27 * f (Aᶜ ∪ C) + 2 / 27 * f (Aᶜ ∩ C) + 4 / 27 * f C +
        4 / 27 * f ((A ∩ C) ∪ (Aᶜ \ C)) + 1 / 27 * f Aᶜ ≤
      NonmonotoneSubmod.Shared.F (fun S => f (S ∩ (Aᶜ ∪ C))) (biasPt A (1 / 3)) := by sorry

end NonmonotoneSubmod.SmoothLS
