import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1143, second paragraph and display (Feige–Mirrokni–Vondrák
2011). Let `f ≥ 0` be submodular on a ground set of `n = |X| ≥ 1` elements, `A ⊆ X`, `B = X \ A`,
and `R = R(A, 1/3)`. For every `C ⊆ X`:
* if `ω_{A,1/3}(x) ≤ (3/n²) OPT` for all `x ∈ B`, then `E[f(R ∪ (B ∩ C))] ≤ E[f(R)] + (2/n) OPT`;
* if `ω_{A,1/3}(x) ≥ -(3/n²) OPT` for all `x ∈ A`, then `E[f(R ∩ (B ∪ C))] ≤ E[f(R)] + (2/n) OPT`. -/
theorem terminal_upper_estimates {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A : Finset X) :
    ((∀ x, x ∉ A → omegaB f A (1 / 3) x ≤ 3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) →
      ∀ C : Finset X, NonmonotoneSubmod.Shared.F (fun S => f (S ∪ (Aᶜ ∩ C))) (biasPt A (1 / 3)) ≤
        Phi f (1 / 3) A + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f) ∧
    ((∀ x, x ∈ A → -(3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ≤ omegaB f A (1 / 3) x) →
      ∀ C : Finset X, NonmonotoneSubmod.Shared.F (fun S => f (S ∩ (Aᶜ ∪ C))) (biasPt A (1 / 3)) ≤
        Phi f (1 / 3) A + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f) := by sorry

end NonmonotoneSubmod.SmoothLS
